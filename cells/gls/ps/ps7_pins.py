"""The PS7_PS7 bel pins the gcd_ps GLS models (M_AXI_GP0 + FCLK), bit-level as
nextpnr names them.  Shared by gls/gen.py (which pins are outputs, port order)
and gls/ps/gen_ps7.py (the Verilog model's port list), so they cannot drift.
Every other PS7 pin is tied off in the routed design and is not modelled."""

def _bus(name, w):
    return ["%s%d" % (name, i) for i in range(w)]

OUTPUTS = (_bus("FCLKCLK", 4) + _bus("MAXIGP0ARADDR", 32) + ["MAXIGP0ARESETN"]
           + _bus("MAXIGP0ARID", 12) + ["MAXIGP0ARVALID"] + _bus("MAXIGP0AWADDR", 32)
           + _bus("MAXIGP0AWID", 12) + ["MAXIGP0AWVALID", "MAXIGP0BREADY", "MAXIGP0RREADY"]
           + _bus("MAXIGP0WDATA", 32) + _bus("MAXIGP0WSTRB", 4) + ["MAXIGP0WVALID"])
INPUTS = (["MAXIGP0ACLK", "MAXIGP0ARREADY", "MAXIGP0AWREADY"] + _bus("MAXIGP0BID", 12)
          + ["MAXIGP0BVALID"] + _bus("MAXIGP0RDATA", 32) + _bus("MAXIGP0RID", 12)
          + ["MAXIGP0RVALID", "MAXIGP0WREADY"])
