package io.kaitai.struct.languages

import io.kaitai.struct.{ClassTypeProvider, RuntimeConfig, Utils}
import io.kaitai.struct.datatype.{DataType, FixedEndian, InheritedEndian, KSError, ValidationNotEqualError, NeedRaw, LittleEndian, BigEndian}
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.LuaTranslator

class WiresharkLuaCompiler(typeProvider: ClassTypeProvider, config: RuntimeConfig)
  extends LuaCompiler(typeProvider, config) {

  import WiresharkLuaCompiler._

  def protoName: String = "proto"

  override def fileHeader(topClassName: String): Unit = {
    outHeader.puts(s"-- $headerComment")
    outHeader.puts("--")
    outHeader.puts("-- This file is compatible with Lua 5.3")
    outHeader.puts

    //importList.add("package.prepend_path(\"plugins/kaitai_struct_lua_runtime\")")
    importList.add("local class = require(\"class\")")
    importList.add("require(\"tvbstream\")")
    importList.add("require(\"kaitaistruct\")")

    val className = type2class(topClassName)
    importList.add(s"local $protoName = Proto('$topClassName', '$className')")
    importList.add(s"$protoName.fields = {}")
    out.puts
    out.puts(s"function ${protoName}.dissector(tvb, pinfo, root)")
    out.inc
    out.puts(s"pinfo.cols.protocol = '$className'")
    out.puts(s"local tree = root:add($protoName, tvb(), '$className')")
    out.puts(s"local io = $kstreamName(TVBStream(tvb))")
    out.puts(s"local obj = $className(io, tree)")
    out.dec
    out.puts("end")
    out.puts("")
  }

  override def fileFooter(topClassName: String): Unit = {
    //out.puts("local udp_port = DissectorTable.get(\"udp.port\")")
    //out.puts(f"udp_port:add(11159, $protoName)")
  }

  override def classConstructorHeader(name: List[String], parentType: DataType, rootClassName: List[String], isHybrid: Boolean, params: List[ParamDefSpec]): Unit = {
    val endianAdd = if (isHybrid) ", is_le" else ""
    val paramsList = Utils.join(params.map((p) => paramName(p.id)), "", ", ", ", ")

    out.puts(s"function ${types2class(name)}:_init($paramsList" + s"io, tree, parent, root$endianAdd)")
    out.inc
    out.puts(s"$kstructName._init(self, io)")
    out.puts("self._parent = parent")
    out.puts("self._root = root or self")
    out.puts("self._tree = tree")
    if (isHybrid)
      out.puts("self._is_le = is_le")

    // Store parameters passed to us
    params.foreach((p) => handleAssignmentSimple(p.id, paramName(p.id)))
  }

  // Maps a Kaitai DataType onto a Wireshark ftypes.* constant. Width-aware
  // (a `b11` field is a UINT16, not a blanket BYTES/UINT32), and unwraps
  // EnumType down to its underlying int type: for an attribute with `enum:`
  // set, dataType *is* EnumType(name, basedOn) - see AttrSpec/DataType.fromYaml
  // - so without unwrapping it here, every enum field fell through to the
  // catch-all "BYTES" case below.
  def attr2wireshark(attrType: DataType): String =
    attrType match {
      case _:BytesLimitType => "BYTES"
      case Int1Type(false) => "UINT8"
      case Int1Type(true) => "INT8"
      case IntMultiType(signed, width, _) =>
        // width was previously ignored here, so every multi-byte int (u2/u4/u8...)
        // was mis-reported as a 32-bit field regardless of its real size.
        val prefix = if (signed) "INT" else "UINT"
        s"$prefix${width.width * 8}"
      case BitsType1(_) => "BOOLEAN"
      case BitsType(width, _) =>
        // bucket by bit width into the smallest ftype that holds it, instead of
        // always falling back to BYTES (which made tree:add reject a plain number).
        if (width <= 8) "UINT8"
        else if (width <= 16) "UINT16"
        else if (width <= 32) "UINT32"
        else "UINT64"
      case FloatMultiType(width, _) =>
        if (width.width == 8) "DOUBLE" else "FLOAT"
      case _:StrType => "STRINGZ"
      case EnumType(_, basedOn) => attr2wireshark(basedOn)
      case _ => "BYTES"
    }

  override def attrUserTypeParse(id: Identifier, dataType: UserType, io: String, rep: RepeatSpec, defEndian: Option[FixedEndian], assignType: DataType): Unit = {
    var tvbCalcSize = true
    var tvb = s"$io._io.tvb(_offset, 0)"
    val newIO = dataType match {
      case knownSizeType: UserTypeFromBytes =>
        // we have a fixed buffer, thus we shall create separate IO for it
        tvb = s"_tvb"
        tvbCalcSize = false
        createSubstream(id, knownSizeType.bytes, io, rep, defEndian)
      case _: UserTypeInstream =>
        // no fixed buffer, just use regular IO
        io
    }
    val expr = parseExpr(dataType, dataType, newIO, defEndian)
    out.puts(s"local _tree = self._tree:add($tvb, '${idToStr(id)}')")
    // FIXME: ignores autoread
    handleAssignment(id, expr, rep, false)
    if (tvbCalcSize) {
      out.puts(s"_tree:set_len($io:pos() - _offset)")
    }
  }

  def protoFieldName(id: Identifier): String = {
    val prefix = typeProvider.nowClass.name.map(x => type2class(x)).mkString("_")
    s"${prefix}_${publicMemberName(id)}"
  }

  // attrParse (CommonReads.scala) calls attrDebugStart(id, attr.dataType, ...)
  // *before* dispatching into attrParse2/parseExpr. For an attribute with
  // `enum:` set, attr.dataType is EnumType(name, basedOn) - the enum wrapper
  // itself, not the underlying int type - and attrParse2's `case t: EnumType`
  // branch then calls parseExpr(t.basedOn, ...) to do the actual read, then
  // wraps the result via translator.doEnumById(...) before assignment. So by
  // the time handleAssignmentSimple runs, self.<field> holds an enum-wrapped
  // Lua value, not a plain number - useless for Wireshark's tree:add, which
  // needs a number matching the field's ftype.
  //
  // We track which attribute (if any) currently being read is enum-typed, so
  // parseExpr can stash the *raw* read result in a `_raw_<name>` local before
  // it gets wrapped, and attrDebugEnd can hand that raw local to Wireshark
  // instead of the enum object.
  private var curEnumAttrId: Option[Identifier] = None

  override def attrDebugStart(attrId: Identifier, attrType: DataType, io: Option[String], rep: RepeatSpec): Unit = {
    curEnumAttrId = attrType match {
      case EnumType(_, _) => Some(attrId)
      case _ => None
    }
    io match {
      case Some(ioStr) => out.puts(s"local _offset = $ioStr:pos()")
      case None => // value instance (computed, not parsed from a stream) - nothing to snapshot
    }
  }

  override def attrDebugEnd(attrName: Identifier, attrType: DataType, io: String, repeat: RepeatSpec): Unit = {
    attrType match {
      case _:UserType | _:SwitchType | _:ArrayType => {}
      case _ =>
        val spec = attr2wireshark(attrType)
        val varName = protoFieldName(attrName)
        val shortName = idToStr(attrName)
        val dotName = typeProvider.nowClass.name.map(x => type2class(x)).mkString(".") + "." + publicMemberName(attrName)

        // For enum fields, build a Wireshark "valuestring" table (raw id -> symbolic
        // name) so the packet tree shows e.g. "(destination_unreachable) 3" instead of just "3". Enum
        // member names are validated KS identifiers, so no quoting/escaping needed.
        val enumSpecOpt = attrType match {
          case et: EnumType => et.enumSpec
          case _ => None
        }
        val protoFieldArgs = enumSpecOpt match {
          case Some(es) =>
            val entries = es.sortedSeq.map { case (id, v) => s"[$id] = '${v.name}'" }.mkString(", ")
            s"'$shortName', '$dotName', ftypes.$spec, {$entries}, base.DEC"
          case None =>
            s"'$shortName', '$dotName', ftypes.$spec"
        }
        // FIXME: hack
        importList.add(s"local $varName = ProtoField.new($protoFieldArgs)")
        importList.add(s"table.insert($protoName.fields, $varName)")

        // For enum fields self.<n> holds the enum-wrapped value, not a plain
        // number - use the raw value stashed by parseExpr() instead.
        val valueSrc = attrType match {
          case EnumType(_, _) => s"_raw_${idToStr(attrName)}"
          case _ => privateMemberName(attrName)
        }
        // Lua numbers can't carry full 64-bit precision; Wireshark's tree:add
        // needs its UInt64/Int64 userdata for ftypes.UINT64/INT64 values.
        val valueExpr = spec match {
          case "UINT64" => s"UInt64($valueSrc)"
          case "INT64" => s"Int64($valueSrc)"
          case _ => valueSrc
        }
        out.puts(s"self._tree:add($varName, $io._io.tvb(_offset, $io:pos() - _offset), $valueExpr)")
    }
  }

  override def parseExpr(dataType: DataType, assignType: DataType, io: String, defEndian: Option[FixedEndian]): String = {
    val raw = dataType match {
      case t: ReadableType =>
        s"$io:read_${t.apiCall(defEndian)}()"
      case blt: BytesLimitType =>
        s"$io:read_bytes(${expression(blt.size)})"
      case _: BytesEosType =>
        s"$io:read_bytes_full()"
      case BytesTerminatedType(terminator, include, consume, eosError, _) =>
        s"$io:read_bytes_term($terminator, $include, $consume, $eosError)"
      case BitsType1(bitEndian) =>
        s"$io:read_bits_int_${bitEndian.toSuffix}(1) ~= 0"
      case BitsType(width: Int, bitEndian) =>
        s"$io:read_bits_int_${bitEndian.toSuffix}($width)"
      case t: UserType =>
        val addParams = Utils.join(t.args.map((a) => translator.translate(a)), "", ", ", ", ")
        val addArgs = if (t.isOpaque) {
          ""
        } else {
          val parent = t.forcedParent match {
            case Some(USER_TYPE_NO_PARENT) => "nil"
            case Some(fp) => translator.translate(fp)
            case None => "self"
          }
          val addEndian = t.classSpec.get.meta.endian match {
            case Some(InheritedEndian) => ", self._is_le"
            case _ => ""
          }
          s", _tree, $parent, self._root$addEndian"
        }
        s"${types2class(t.classSpec.get.name)}($addParams$io$addArgs)"
    }

    // If attrDebugStart just told us this read belongs to an enum-typed
    // attribute, capture the raw value in a named local instead of returning
    // the read expression directly. Whatever wraps our return value in an
    // enum lookup (translator.doEnumById) will then wrap the local's name
    // instead of the raw read call, e.g.:
    //   local _raw_subtype = self._io:read_u1()
    //   self.subtype = Ieee1722Simple1.SubtypeEnum(_raw_subtype)
    // ...leaving `_raw_subtype` available for attrDebugEnd to hand to Wireshark.
    curEnumAttrId match {
      case Some(attrId) =>
        curEnumAttrId = None
        val rawVar = s"_raw_${idToStr(attrId)}"
        out.puts(s"local $rawVar = $raw")
        rawVar
      case None =>
        raw
    }
  }

  override def allocateIO(varName: Identifier, rep: RepeatSpec): String = {
    val varStr = privateMemberName(varName)

    val args = getRawIdExpr(varName, rep)

    out.puts("local _tvb = self._io._io.tvb(_offset, self._io:pos() - _offset)")
    out.puts(s"local _io = $kstreamName(TVBStream(_tvb))")
    "_io"
  }
}

object WiresharkLuaCompiler extends LanguageCompilerStatic
    with UpperCamelCaseClasses
    with StreamStructNames
    with ExceptionNames {
  override def getCompiler(
    tp: ClassTypeProvider,
    config: RuntimeConfig
  ): LanguageCompiler = new WiresharkLuaCompiler(tp, config)

  def idToStr(id: Identifier): String =
    id match {
      case SpecialIdentifier(name) => name
      case NamedIdentifier(name) => name
      case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
      case InstanceIdentifier(name) => s"_m_$name"
      case RawIdentifier(innerId) => s"_raw_${idToStr(innerId)}"
    }

  def publicMemberName(id: Identifier): String =
    id match {
      case InstanceIdentifier(name) => name
      case _ => idToStr(id)
    }

  override def kstructName: String = "KaitaiStruct"
  override def kstreamName: String = "KaitaiStream"
  override def ksErrorName(err: KSError): String = err.name

  def types2class(name: List[String]): String =
    name.map(x => type2class(x)).mkString(".")
}
