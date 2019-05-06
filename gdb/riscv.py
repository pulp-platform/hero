import struct
import json

XLEN = 64

# FIXME: for some registers the proper value is already retrieved but not for every register unfortunately
def cv64unsigned(val):
    try:
        pkd = struct.pack('>q', int(val))
        return struct.unpack('>Q', pkd)[0]
    except struct.error:
        return int(val)

def tpidxs(idxs):
    if isinstance(idxs, int):
        idxs = (idxs, idxs)
    return idxs

class RVCommand(gdb.Command):
    """RV base command"""

    def __init__ (self):
        super (RVCommand, self).__init__("rv", gdb.COMMAND_USER, prefix = True)

    def invoke (self, arg, from_tty):
        print("rv (RISCV) must be followed by rv command")
        print("List of rv subcommands")
        print()
        print("rv reg -- Get and set registers")
        print("rv mem -- Interact with memory")

RVCommand()

class RVRegCommand(gdb.Command):
    """RV reg command"""

    def __init__ (self):
        super (RVRegCommand, self).__init__("rv reg", gdb.COMMAND_USER, prefix = True)

    def invoke (self, arg, from_tty):
        print("rv (RISCV) get must be followed by rv get command")
        print("List of rv get subcommands")
        print()
        print("rv reg get -- Get register")
        print("rv reg set -- Set register")

RVRegCommand()

REG = \
    {"misa":
       {
           "MXL": (XLEN-2, XLEN-1),
       },
       "mstatus":
       {
           "SD": XLEN-1,
           "SXL": (34, 35),
           "UXL": (32, 33),
           "MXR": 19,
           "SUM": 18,
           "MPRV": 17,
           "XS": (15, 16),
           "FS": (13, 14),
           "MPP": (11, 12),
           "SPP": 8,
           "MPIE": 7,
           "SPIE": 5,
           "UPIE": 4,
           "MIE": 3,
           "SIE": 1,
           "UIE": 0
       },
       "sstatus":
       {
           "SD": XLEN-1,
           "UXL": (32, 33),
           "MXR": 19,
           "SUM": 18,
           "XS": (15, 16),
           "FS": (13, 14),
           "SPP": 8,
           "SPIE": 5,
           "UPIE": 4,
           "SIE": 1,
           "UIE": 0
       },
       "satp":
       {
           "MODE": (60, 63),
           "ASID": (44, 59),
           "PPN": (0, 43)
       },
       "dcsr":
       {
           "XDEBUGVER": (28, 31),
           "EBREAKM": 15,
           "EBREAKS": 13,
           "EBREAKU": 12,
           "STEPIE": 11,
           "STOPCOUNT": 10,
           "STOPTIME": 9,
           "CAUSE": (6, 8),
           "MPRVEN": 4,
           "NMIP": 3,
           "STEP": 2,
           "PRV": (0, 1)
       }
    }

# COMMAND TO GET ALL THE FIELDS FOR CONFIGURATION REGISTERS
class RVRegGetCommand (gdb.Command):
    """Get registers."""

    def __init__ (self):
        super (RVRegGetCommand, self).__init__ ("rv reg get", gdb.COMMAND_USER)

    def invoke (self, arg, from_tty):
        args = gdb.string_to_argv(arg)
        if len(args) != 1:
            raise gdb.GdbError("expects single argument")
        name = args[0]
        frame = gdb.selected_frame()
        reg = ""
        try:
            reg = cv64unsigned(frame.read_register(name))
        except ValueError:
            raise gdb.GdbError("invalid register name")

        breg = "{:064b}".format(reg)
        print("{}\n\nb: {}\nd: {}\nh: {:#x}".format(name, breg, reg, reg))
        if name in REG:
            vd = REG[name]
            ibreg = breg[::-1]
            res = {key:(int(ibreg[value]) if isinstance(value, int) else int((ibreg[value[0]:value[1]+1])[::-1], 2)) for (key, value) in list(vd.items())}
            print("f: {}".format(json.dumps(res, sort_keys = True, indent = 4)))

RVRegGetCommand()

# COMMAND TO SET CONFIGURATION REGISTERS FIELDS DIRECTLY
class RVRegSetCommand (gdb.Command):
    """Set registers."""

    def __init__ (self):
        super (RVRegSetCommand, self).__init__ ("rv reg set", gdb.COMMAND_USER)

    def invoke (self, arg, from_tty):
        args = gdb.string_to_argv(arg)
        if len(args) < 2 or len(args) > 3:
            raise gdb.GdbError("expects two or three arguments")
        name = args[0]
        frame = gdb.selected_frame()
        try:
            frame.read_register(name)
        except ValueError:
            raise gdb.GdbError("invalid register name")

        if len(args) == 2:
            val = args[1]
            gdb.execute('set $' + str(name) + " = 0d" + str(val))
        else:
            if name not in REG:
                raise gdb.GdbError("register does not support fields")

            field, val = args[1:3]
            field = field.upper()
            val = int(val)

            if field not in REG[name]:
                raise gdb.GdbError("invalid register field")
            if val < 0:
                raise gdb.GdbError("value has to be positive")

            idxs = tpidxs(REG[name][field])
            breg = "{:064b}".format(cv64unsigned(frame.read_register(name)))

            bval = "{:b}".format(val)
            slen = (idxs[1] - idxs[0] + 1)
            if len(bval) > slen:
                raise gdb.GdbError("value too large")
            bval = '0'*(slen - len(bval)) + bval

            ibreg = breg[::-1]
            nbreg = (ibreg[:idxs[0]] + bval[::-1] + ibreg[idxs[1]+1:])[::-1]
            nval = int(nbreg, 2)
            gdb.execute('set $' + str(name) + " = 0d" + str(nval))

RVRegSetCommand()

class RVMemCommand(gdb.Command):
    """RV mem command"""

    def __init__ (self):
        super (RVMemCommand, self).__init__("rv mem", gdb.COMMAND_USER, prefix = True)

    def invoke (self, arg, from_tty):
        print("rv (RISCV) mem must be followed by rm mem command")
        print("List of rv mem subcommands")
        print()
        print("rv mem phys -- Get physical address")
        print("rv mem auto -- Automatic address conversion in debug mode")

RVMemCommand()

# UTILITY FUNCTION TO CONVERT VIRTUAL TO PHYSICAL ADDRESS USING RISCV SV39 STRUCTURE
PAGE_SIZE = 4096
PTE_FMT = {
    "PPN2": (28, 53),
    "PPN1": (19, 27),
    "PPN0": (10, 18),
    "PPN": (10, 53),
    "RSW": (8, 9),
    "D": 7,
    "A": 6,
    "G": 5,
    "U": 4,
    "X": 3,
    "W": 2,
    "R": 1,
    "V": 0
}
PTE_POFF = [10, 19, 28, 54]
PTE_VOFF = [12, 21, 30, 39]
PTE_LEVELS = 3
PTE_SIZE = 8

def physical(virt):
    bvirt = "{:064b}".format(virt)

    satp = cv64unsigned(gdb.selected_frame().read_register("satp"))
    idxs = tpidxs(REG['satp']['PPN'])
    ppn = int((("{:064b}".format(satp)[::-1])[idxs[0]:idxs[1]+1])[::-1], 2)

    inf = gdb.selected_inferior()
    a = ppn * PAGE_SIZE
    i = PTE_LEVELS - 1
    while True:
        vpn = int(bvirt[::-1][PTE_VOFF[i]:PTE_VOFF[i+1]][::-1], 2)

        mem = inf.read_memory(a + vpn*PTE_SIZE, 8)[::-1]
        pte = int("".join("{:02x}".format(ord(c)) for c in mem), 16)
        bpte = "{:064b}".format(pte)
        ibpte = bpte[::-1]
        pter = {key:(int(ibpte[value]) if isinstance(value, int) else int((ibpte[value[0]:value[1]+1])[::-1], 2)) for (key, value) in list(PTE_FMT.items())}

        # print("{} {}".format(i, json.dumps(pter, sort_keys = True, indent = 4)), hex(pter['PPN']*4096))

        if pter['V'] == 0:
            return None
        if pter['R'] == 0 and pter['W'] == 1:
            raise RuntimeError("invalid pte flags")

        if pter['R'] == 1 or pter['W'] == 1:
            if i > 0 and int(ibpte[PTE_POFF[0]:PTE_POFF[i]][::-1], 2) != 0:
                raise RuntimeError('misaligned superpage')

            phys = bvirt[::-1][:12] + bvirt[::-1][PTE_VOFF[0]:PTE_VOFF[i]] + ibpte[PTE_POFF[i]:PTE_POFF[PTE_LEVELS]] + '0'*8
            return int(phys[::-1], 2)

        a = pter['PPN'] * PAGE_SIZE
        i = i - 1

        if i < 0:
            raise RuntimeError("lowest level pte is not a leaf")

# COMMAND TO CONVERT TO PHYSICAL ADDRESS USING THE MEMORY SYSTEM
class RVMemPhysCommand(gdb.Command):
    """Get physical address of argument"""

    def __init__ (self):
        super (RVMemPhysCommand, self).__init__("rv mem phys", gdb.COMMAND_USER)

    def invoke (self, arg, from_tty):
        args = gdb.string_to_argv(arg)
        if len(args) != 1:
            raise gdb.GdbError("expects one argument")

        virt = int(cv64unsigned(gdb.parse_and_eval('{}'.format(args[0]))))
        phys = physical(virt)
        if phys is None:
            print('not mapped')
        else:
            print((hex(phys)))
            gdb.execute("set var $_ = 0d" + str(phys))

RVMemPhysCommand()

# COMMAND TO AUTOMATE CONVERSION OF PROGRAM COUNTER TO PHYSICAL ADDRESS
class RVMemAutoCommand(gdb.Command):
    """Enable automatic conversion of pc to physical address on stop/continue"""

    def __init__ (self):
        super (RVMemAutoCommand, self).__init__("rv mem auto", gdb.COMMAND_USER)
        self.enabled = False
        self.phys = 0x0
        self.virt = 0x0

    def hook_stop(self, event):
        self.virt = gdb.selected_frame().pc()
        try:
            self.phys = int(gdb.parse_and_eval(gdb.execute("rv mem phys 0d" + str(self.virt), to_string = True)))
        except gdb.error:
            self.phys = self.virt
        gdb.execute("set $pc = 0d" + str(self.phys))

    def hook_continue(self, event):
        gdb.execute("set $pc = 0d" + str(self.virt))

    def invoke (self, arg, from_tty):
        if self.enabled:
            self.enabled = False
            self.hook_continue(None)
            gdb.events.stop.disconnect(self.hook_stop)
            gdb.events.cont.disconnect(self.hook_continue)
        else:
            self.enabled = True
            self.hook_stop(None)
            gdb.events.stop.connect(self.hook_stop)
            gdb.events.cont.connect(self.hook_continue)

RVMemAutoCommand()
