# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

"""Generate a SystemRDL description of the block"""

import re
from dataclasses import dataclass
from typing import TextIO, Any
from pathlib import Path
import shutil

import reggen
from reggen.ip_block import IpBlock
from reggen.reg_block import RegBlock
from reggen.register import Register
from reggen.multi_register import MultiRegister
from reggen.window import Window
from reggen.field import Field
from reggen.access import SWAccess, HWAccess, HwAccess
from reggen.inter_signal import InterSignal
from reggen.signal import Signal
from reggen.bus_interfaces import BusInterfaces
from reggen.interrupt import Interrupt
from reggen.alert import Alert
from reggen.params import LocalParam
from reggen.clocking import Clocking
from reggen.exporter import Exporter
from reggen.systemrdl.udp import register_udps

import systemrdl.component
from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.messages import FileSourceRef  # type: ignore[attr-defined]
from systemrdl.importer import RDLImporter
from systemrdl.component import Addrmap
from systemrdl.core.parameter import Parameter
from systemrdl import rdltypes
from systemrdl.rdltypes import AccessType, OnReadType, OnWriteType  # type: ignore[attr-defined]
from systemrdl.ast.references import InstRef
from rdlexporter import RdlExporter


def sanitize_str(s: str) -> str:
    substitutions = [(r"\\:", ":"), ("`", ""), (r"\n", ""), ('''"''', '''\\"''')]
    for pattern, replacement in substitutions:
        s = re.sub(pattern, replacement, s)
    return s


@dataclass
class HWAccess2Systemrdl:
    inner: HWAccess

    # Maps reggen hardware access property to SystemRDL properties. Each line in this table is
    # a set of RDL properties where:
    #    hw: Hardware read and write access
    MAP = {
        HwAccess.HRO: {"hw": AccessType.r},
        HwAccess.HRW: {"hw": AccessType.rw},
        HwAccess.HWO: {"hw": AccessType.w},
        HwAccess.NONE: {"hw": AccessType.na},
    }

    def export(self) -> dict[str, object]:
        return self.MAP[self.inner.value[1]]


@dataclass
class SWAccess2Systemrdl:
    inner: SWAccess

    # Maps reggen software access property to SystemRDL properties. Each line in this table is
    # a set of RDL properties where:
    #   sw: Software read and write access.
    #   onread: Side effect when software reads.
    #   onwrite: Side effect when software writes.
    MAP = {
        "ro": {"sw": AccessType.r},
        "rw": {"sw": AccessType.rw},
        "wo": {"sw": AccessType.w},
        "rc": {"sw": AccessType.rw, "onread": OnReadType.rclr},
        "r0w1c": {"sw": AccessType.w, "onwrite": OnWriteType.woclr},
        "rw1c": {"sw": AccessType.rw, "onwrite": OnWriteType.woclr},
        "rw0c": {"sw": AccessType.rw, "onwrite": OnWriteType.wzc},
        "rw1s": {"sw": AccessType.rw, "onwrite": OnWriteType.woset},
        "none": {"sw": AccessType.na},
    }

    def export(self) -> dict[str, object]:
        return self.MAP[self.inner.key]


@dataclass
class Field2Systemrdl:
    inner: Field
    importer: RDLImporter
    root: Addrmap
    parent: systemrdl.component.Component

    def _get_mubi_name(self) -> str:
        alignment = 4
        aligned_width = (self.inner.bits.width() + alignment - 1) & ~(alignment - 1)
        return f"MultiBitBool{aligned_width}"

    def assign_swwe(self, field: systemrdl.component.Component, regwen: str | None) -> None:
        if swwe := bool(regwen):
            property_name = "swwe"
            if reg_ref := self.root.get_child_by_name(str(regwen)):
                wen_field = reg_ref.children[0]
                # This is a workaround and shall be fixed when the Issue
                # https://github.com/SystemRDL/systemrdl-compiler/issues/183 is fixed.
                swwe = InstRef(
                    self.importer.compiler.env,
                    self.root,
                    [(str(regwen), [], None), (str(wen_field.inst_name), [], None)],
                )  # type: ignore
                if wen_field.width > 1:  # type: ignore
                    property_name = "mubi_swwe"
            self.importer.assign_property(field, property_name, swwe)

    def export(
        self, strip_suffix: bool = False, regwen: str | None = None
    ) -> systemrdl.component.Field:
        # Workaround because reggen adds the register index to all multiregisters fields,
        # although it only makes sense when multiregisters are compacted (collapsed)
        # to avoid name colision.

        name = re.sub(r"_\d+$", "", self.inner.name) if strip_suffix else self.inner.name

        rdl_t = self.importer.create_field_definition(name)
        field = self.importer.instantiate_field(
            rdl_t, name.upper(), self.inner.bits.lsb, self.inner.bits.width()
        )

        swaccess = SWAccess2Systemrdl(self.inner.swaccess).export()
        self.importer.assign_property(field, "sw", swaccess["sw"])
        if "onread" in swaccess:
            self.importer.assign_property(field, "onread", swaccess["onread"])
        if "onwrite" in swaccess:
            self.importer.assign_property(field, "onwrite", swaccess["onwrite"])

        hwaccess = HWAccess2Systemrdl(self.inner.hwaccess).export()
        self.importer.assign_property(field, "hw", hwaccess["hw"])

        if self.inner.resval is not None:
            self.importer.assign_property(field, "reset", self.inner.resval)

        if self.inner.hwqe:
            self.importer.assign_property(field, "swmod", self.inner.hwqe)

        if self.inner.desc:
            self.importer.assign_property(field, "desc", sanitize_str(self.inner.desc))

        if self.inner.mubi:
            mubi_enum_name = self._get_mubi_name()
            enum = self.importer.compiler.namespace.lookup_type(mubi_enum_name)
            self.importer.assign_property(field, "encode", enum)

        self.assign_swwe(field, regwen)

        return field

    def post_process(self, regwen: str) -> None:
        if field := self.parent.get_child_by_name(self.inner.name.upper()):
            self.assign_swwe(field, regwen)


@dataclass
class Window2Systemrdl:
    inner: Window
    importer: RDLImporter

    def export(self) -> systemrdl.component.Mem:
        rdl_mem_t = self.importer.create_mem_definition(self.inner.name)
        memwidth = self.inner.size_in_bytes // self.inner.items
        self.importer.assign_property(rdl_mem_t, "memwidth", memwidth * 8)
        self.importer.assign_property(rdl_mem_t, "mementries", self.inner.items)

        swaccess = SWAccess2Systemrdl(self.inner.swaccess).export()
        self.importer.assign_property(rdl_mem_t, "sw", swaccess["sw"])

        if self.inner.data_intg_passthru:
            self.importer.assign_property(rdl_mem_t, "integrity_bypass", True)

        return self.importer.instantiate_mem(rdl_mem_t, self.inner.name.upper(), self.inner.offset)


class Register2Systemrdl:
    inner: list[Register]
    importer: RDLImporter
    root: Addrmap
    stride: int | None = None
    count: int | None = None
    strip_suffix: bool = False
    name: str = ""
    compacted: bool = False

    def __init__(self, reg: MultiRegister | Register, importer: RDLImporter, root: Addrmap):
        self.importer = importer
        self.root = root
        if isinstance(reg, Register):
            self.inner = [reg]
            self.name = reg.name
        elif isinstance(reg, MultiRegister):
            if len(reg.cregs) > 1 and reg.compact and reg.get_n_bits() % 32:
                # There're cases where the number of fields can't fit into a round number of
                # registers which makes it unfit for a systemrdl array.
                self.inner = reg.cregs
            else:
                # This will be a systermrdl array.
                self.inner = reg.cregs[0:1]
                self.stride = reg.stride
                self.count = len(reg.cregs)
                self.compacted = reg.compact
                # Workaround because reggen adds the register index to all multiregisters fields,
                # although it only makes sense when multiregisters are compacted (collapsed)
                # to avoid name colision.
                self.strip_suffix = not self._has_name_colision(reg)
                self.name = re.sub(r"_\d+$", "", self.inner[0].name)

    def export(self) -> list[systemrdl.component.Reg]:
        res = []
        for reg in self.inner:
            name = self.name or reg.name or "Register"
            reg_type = self.importer.create_reg_definition(name)
            reg_inst = self.importer.instantiate_reg(
                reg_type,
                name.upper(),
                reg.offset,
                [self.count] if self.count else None,
                self.stride if self.stride else None,
            )

            for rfield in reg.fields:
                field = Field2Systemrdl(rfield, self.importer, self.root, reg_inst).export(
                    self.strip_suffix, reg.regwen
                )
                self.importer.add_child(reg_inst, field)

            reg_inst.external = reg.hwext

            if self.compacted:
                self.importer.assign_property(reg_inst, "compacted", True)

            if reg.hwre:
                self.importer.assign_property(reg_inst, "hwre", reg.hwre)

            if reg.shadowed:
                self.importer.assign_property(reg_inst, "shadowed", reg.shadowed)

            if reg.desc:
                self.importer.assign_property(reg_inst, "desc", sanitize_str(reg.desc))

            if reg.async_clk:
                name = reg.async_clk[1].clock or "Clock"
                if sig_ref := self.root.get_child_by_name(name.upper()):
                    # This is a workaround and shall be fixed when the Issue
                    # https://github.com/SystemRDL/systemrdl-compiler/issues/276 is fixed.
                    sig_name = sig_ref.inst_name or "Clock"
                    async_clk = InstRef(
                        self.importer.compiler.env,
                        self.root,
                        [(sig_name, [], None)],
                    )
                    self.importer.assign_property(reg_inst, "async_clk", async_clk)

                reset_name = reg.async_clk[1].reset or "reset"
                if sig_ref := self.root.get_child_by_name(reset_name.upper()):
                    sig_name = sig_ref.inst_name or "reset"
                    async_rst = InstRef(
                        self.importer.compiler.env,
                        self.root,
                        [(sig_name, [], None)],
                    )
                    self.importer.assign_property(reg_inst, "async_rst", async_rst)

            res.append(reg_inst)
        return res

    def post_process(self) -> None:
        for reg in self.inner:
            if reg.regwen and (reg_inst := self.root.get_child_by_name(reg.name.upper())):
                for rfield in reg.fields:
                    Field2Systemrdl(rfield, self.importer, self.root, reg_inst).post_process(
                        reg.regwen
                    )

    def _has_name_colision(self, reg: MultiRegister) -> bool:
        names = set([re.sub(r"_\d+$", "", f.name) for f in reg.cregs[0].fields])
        return len(names) != len(reg.cregs[0].fields)


@dataclass
class RegBlock2Systemrdl:
    inner: RegBlock
    importer: RDLImporter

    def export(self, addrmap: Addrmap | None = None) -> Addrmap | None:
        if not addrmap:
            name = self.inner.name or "Block"
            rdl_addrmap_t = self.importer.create_addrmap_definition(name)
            addrmap = self.importer.instantiate_addrmap(rdl_addrmap_t, name.upper(), 0)

        # registers and multiregs
        for reg in self.inner.registers:
            self.importer.add_child(
                addrmap, Register2Systemrdl(reg, self.importer, addrmap).export()[0]
            )

        for reg in self.inner.registers:
            Register2Systemrdl(reg, self.importer, addrmap).post_process()

        # multiregs
        for mreg in self.inner.multiregs:
            _regs = Register2Systemrdl(mreg, self.importer, addrmap).export()
            for reg in _regs:  # type: ignore
                self.importer.add_child(addrmap, reg)  # type: ignore

        # windows
        for window in self.inner.windows:
            self.importer.add_child(addrmap, Window2Systemrdl(window, self.importer).export())

        nonempty = bool(
            len(self.inner.registers) + len(self.inner.multiregs) + len(self.inner.windows)
        )
        return addrmap if nonempty else None


@dataclass
class InterSignal2Systemrdl:
    inner: InterSignal
    importer: RDLImporter

    def export(self) -> systemrdl.component.Signal:
        rdl_t = self.importer._create_definition(systemrdl.component.Signal, self.inner.name, None)
        signal = self.importer._instantiate(rdl_t, self.inner.name.upper(), None)

        if self.inner.desc:
            self.importer.assign_property(signal, "desc", sanitize_str(self.inner.desc))

        if isinstance(self.inner.width, int):
            self.importer.assign_property(signal, "signalwidth", self.inner.width)
        elif isinstance(self.inner.width, reggen.params.Parameter):
            self.importer.assign_property(signal, "signalwidth", self.inner.width.default)

        enum_variant = "InterModReqRsp"
        if self.inner.signal_type == "uni":
            enum_variant = "InterModReq" if self.inner.act == "req" else "InterModRecv"
        enum = self.importer.compiler.namespace.lookup_type("SigType")
        if not isinstance(enum, rdltypes.user_enum.UserEnumMeta):
            raise RuntimeError("SigType enum defined or precompiled")
        # The options are: SigType::InterModReqRsp, SigType::InterModReq, SigType::InterModRecv
        self.importer.assign_property(signal, "sigtype", enum[enum_variant])

        if self.inner.struct:
            self.importer.assign_property(signal, "inter_mod_struct", self.inner.struct)

        if self.inner.package:
            self.importer.assign_property(signal, "inter_mod_package", self.inner.package)

        return signal


@dataclass
class Signal2Systemrdl:
    inner: Signal
    importer: RDLImporter
    signal_type: str | None = None

    def export(self) -> systemrdl.component.Signal:
        rdl_t = self.importer._create_definition(systemrdl.component.Signal, self.inner.name, None)
        signal = self.importer._instantiate(rdl_t, self.inner.name.upper(), None)

        if self.inner.desc:
            self.importer.assign_property(signal, "desc", sanitize_str(self.inner.desc))

        self.importer.assign_property(signal, "signalwidth", self.inner.bits.width())

        if isinstance(self.inner, Interrupt):
            enum_variant = "Interrupt"
        elif isinstance(self.inner, Alert):
            enum_variant = "Alert"
        elif self.signal_type:
            enum_variant = self.signal_type
        else:
            raise RuntimeError(f"Signal not supported {self.inner.name}.")

        enum = self.importer.compiler.namespace.lookup_type("SigType")
        if not isinstance(enum, rdltypes.user_enum.UserEnumMeta):
            raise RuntimeError("SigType enum defined or precompiled")
        self.importer.assign_property(signal, "sigtype", enum[enum_variant])
        return signal


@dataclass
class Clocking2Systemrdl:
    inner: Clocking
    importer: RDLImporter

    def export(self) -> list[systemrdl.component.Signal]:
        signals = []
        enum_variant = "Sync"
        enum = self.importer.compiler.namespace.lookup_type("SigType")
        assert isinstance(enum, rdltypes.user_enum.UserEnumMeta)
        rdl_t = self.importer._create_definition(systemrdl.component.Signal, "sync_t", None)

        for item in self.inner.items:
            if item.clock:
                signal = self.importer._instantiate(rdl_t, str(item.clock).upper(), None)
                self.importer.assign_property(signal, "signalwidth", 1)
                self.importer.assign_property(signal, "sigtype", enum[enum_variant])
                signals.append(signal)

            if item.reset:
                signal = self.importer._instantiate(rdl_t, str(item.reset).upper(), None)
                self.importer.assign_property(signal, "signalwidth", 1)
                self.importer.assign_property(signal, "sigtype", enum[enum_variant])
                signals.append(signal)

        return signals


@dataclass
class BusInterfaces2Systemrdl:
    inner: BusInterfaces
    importer: RDLImporter

    def _get_direction(self, interface_name: str = "") -> str:
        if len(self.inner.racl_support) == 1:
            return (
                "Device"
                if self.inner.has_unnamed_device and not self.inner.has_unnamed_host
                else "Host"
            )
        return "Device" if interface_name in self.inner.named_devices else "Host"

    def _get_protocol(self, interface_name: str = "") -> str:
        return "TlUl"

    def _get_hier_path(self, interface_name: str = "") -> str:
        if len(self.inner.device_hier_paths) == 1:
            return list(self.inner.device_hier_paths.values())[0]
        return self.inner.device_hier_paths[interface_name]

    def _get_racl_support(self, interface_name: str = "") -> bool:
        if len(self.inner.racl_support) == 1:
            return list(self.inner.racl_support.values())[0]
        return self.inner.racl_support[interface_name]

    def export(self, interface_name: str = "") -> Any:
        BusInterfaceCfg = self.importer.compiler.namespace.lookup_type("BusInterfaceCfg")
        assert isinstance(BusInterfaceCfg, rdltypes.user_struct.UserStructMeta)
        BusDirection = self.importer.compiler.namespace.lookup_type("BusDirection")
        assert isinstance(BusDirection, rdltypes.user_enum.UserEnumMeta)
        BusProtocol = self.importer.compiler.namespace.lookup_type("BusProtocol")
        assert isinstance(BusProtocol, rdltypes.user_enum.UserEnumMeta)

        instance = BusInterfaceCfg(
            {
                "racl_support": self._get_racl_support(interface_name),
                "direction": BusDirection[self._get_direction(interface_name)],
                "protocol": BusProtocol[self._get_protocol(interface_name)],
                "hier_path": self._get_hier_path(interface_name),
            }
        )
        return instance


@dataclass
class LocalParam2Systemrdl:
    inner: LocalParam

    def get_value(self) -> int:
        bases = {"h": 16, "d": 10, "b": 2}
        value = self.inner.value
        base = 10
        if match := re.match(r"\d+'([hdb])(.*)", value):
            base = bases[match[1]]
            value = match[2]
        return int(value, base)

    def export(self) -> Parameter:
        value = self.get_value()
        name = self.inner.name
        rdl_param = Parameter(rdltypes.get_rdltype(value), name)
        rdl_param._value = value
        return rdl_param


@dataclass
class IpBlock2Systemrdl:
    inner: IpBlock
    importer: RDLImporter

    def export(self) -> Addrmap | None:
        rdl_addrmap = self.importer.create_addrmap_definition(self.inner.name)

        for param in self.inner.params.get_localparams():
            param = LocalParam2Systemrdl(param).export()  # type: ignore
            rdl_addrmap.parameters_dict[param.name] = param  # type: ignore

        for inter_sig in self.inner.inter_signals:
            signal = InterSignal2Systemrdl(inter_sig, self.importer).export()
            rdl_addrmap.children.append(signal)

        for interrupt in self.inner.interrupts:
            signal = Signal2Systemrdl(interrupt, self.importer).export()
            rdl_addrmap.children.append(signal)

        for alert in self.inner.alerts:
            signal = Signal2Systemrdl(alert, self.importer).export()
            rdl_addrmap.children.append(signal)

        for signal in Clocking2Systemrdl(self.inner.clocking, self.importer).export():
            rdl_addrmap.children.append(signal)

        for xputs, direction in zip(self.inner.xputs, ["InOut", "Input", "Output"]):
            for xput in xputs:
                signal = Signal2Systemrdl(xput, self.importer, direction).export()
                rdl_addrmap.children.append(signal)

        bus_interfaces = BusInterfaces2Systemrdl(self.inner.bus_interfaces, self.importer)
        interfaces = list(self.inner.reg_blocks.values())
        if len(interfaces) == 1 and not bool(interfaces[0].name):
            # If there's only one interface, the registers can go directly on the root addressmap.
            RegBlock2Systemrdl(interfaces[0], self.importer).export(rdl_addrmap)

            val = bus_interfaces.export()
            self.importer.assign_property(rdl_addrmap, "bus_interface_cfg", val)
            return rdl_addrmap

        num_children = 0
        for rb in interfaces:
            rdl_rb = RegBlock2Systemrdl(rb, self.importer).export()

            # Skip empty interfaces
            if rdl_rb is None:
                continue

            val = bus_interfaces.export(rb.name)
            self.importer.assign_property(rdl_rb, "bus_interface_cfg", val)
            self.importer.add_child(rdl_addrmap, rdl_rb)
            num_children += 1

        if num_children > 1:
            rdl_addrmap.properties["bridge"] = True

        return rdl_addrmap if num_children else None


def check_rdl(rdl: Path) -> None:
    compiler = RDLCompiler()
    try:
        compiler.compile_file(rdl)
        compiler.elaborate()
    except Exception as e:
        raise RuntimeError(f"Error while compiling {rdl}.") from e


class SystemrdlExporter(Exporter):
    def export(self, outfile: TextIO) -> int:
        comp = RDLCompiler()
        udp_path = register_udps(comp)

        imp = RDLImporter(comp)
        imp.default_src_ref = FileSourceRef(outfile.name)

        try:
            rdl_addrmap = IpBlock2Systemrdl(self.block, imp).export()
        except Exception as e:
            raise RuntimeError(f"Error while building RDL AST for {self.block.name}.") from e

        if rdl_addrmap is None:
            raise RuntimeError("Block {self.block.name} has no registers or windows.")

        imp.register_root_component(rdl_addrmap)

        # At this point, we actually have to close outfile and then pass its path
        # to exp.export (which expects a path rather than a stream).
        outfile.close()

        outpath = Path(outfile.name)
        # Include the user defined enums and properties.
        with outpath.open("w") as f:
            f.write(f'`include "{udp_path.name}"\n\n')
        # Copy the inlcude file to the output dir.
        shutil.copy(udp_path, outpath.parent / udp_path.name)

        try:
            RdlExporter(comp).export(outpath)
        except Exception as e:
            raise RuntimeError(f"Error exporting {self.block.name} to RDL.") from e

        print(f"Successfully generated {outfile.name}, {outpath.parent / udp_path.name}")

        check_rdl(outpath)
        print(f"Successfully generated {outfile.name}, {outpath.parent / udp_path.name}")
        return 0
