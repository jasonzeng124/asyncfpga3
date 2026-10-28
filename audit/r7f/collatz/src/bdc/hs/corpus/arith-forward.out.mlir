module {
  handshake.func @addiFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i16> to <i17>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i8> to <i17>
    %2 = addi %1, %0 {handshake.name = "addi0"} : <i17>
    %3 = extsi %2 {handshake.name = "extsi2"} : <i17> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @addiFW_extui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i17>
    %1 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i8> to <i17>
    %2 = addi %1, %0 {handshake.name = "addi0"} : <i17>
    %3 = extui %2 {handshake.name = "extui2"} : <i17> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @addiFW_extsi_extui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i18>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i18>
    %2 = addi %1, %0 {handshake.name = "addi0"} : <i18>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i18> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @addiFW_extui_extsi(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i16> to <i17>
    %1 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i17>
    %2 = addi %1, %0 {handshake.name = "addi0"} : <i17>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i17> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @subiFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i16> to <i17>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i8> to <i17>
    %2 = subi %1, %0 {handshake.name = "subi0"} : <i17>
    %3 = extsi %2 {handshake.name = "extsi2"} : <i17> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @subiFW_ui_si(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i10>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i10>
    %2 = subi %1, %0 {handshake.name = "subi0"} : <i10>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i10> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @subiFW_si_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i18>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i18>
    %2 = subi %1, %0 {handshake.name = "subi0"} : <i18>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i18> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @subiFW_ui_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i17>
    %1 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i8> to <i17>
    %2 = subi %1, %0 {handshake.name = "subi0"} : <i17>
    %3 = extsi %2 {handshake.name = "extsi0"} : <i17> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @muliFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i16> to <i24>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i8> to <i24>
    %2 = muli %1, %0 {handshake.name = "muli0"} : <i24>
    %3 = extsi %2 {handshake.name = "extsi2"} : <i24> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @muliFW_ui_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i24>
    %1 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i8> to <i24>
    %2 = muli %1, %0 {handshake.name = "muli0"} : <i24>
    %3 = extui %2 {handshake.name = "extui2"} : <i24> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @muliFW_si_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i24>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i24>
    %2 = muli %1, %0 {handshake.name = "muli0"} : <i24>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i24> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @andiFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i16> to <i8>
    %1 = andi %arg0, %0 {handshake.name = "andi0"} : <i8>
    %2 = extui %1 {handshake.name = "extui0"} : <i8> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @oriFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i16>
    %1 = ori %0, %arg1 {handshake.name = "ori0"} : <i16>
    %2 = extui %1 {handshake.name = "extui1"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @xoriFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i16>
    %1 = xori %0, %arg1 {handshake.name = "xori0"} : <i16>
    %2 = extui %1 {handshake.name = "extui1"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shliFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.name = "extsi0"} : <i16> to <i32>
    %1 = constant %arg1 {handshake.name = "constant0", value = 4 : i32} : <>, <i32>
    %2 = shli %0, %1 {handshake.name = "shli0"} : <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shrsi_small(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 4 : i16} : <>, <i16>
    %1 = shrsi %arg0, %0 {handshake.name = "shrsi0"} : <i16>
    %2 = extsi %1 {handshake.name = "extsi0"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shrsi_oob(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.name = "extsi0"} : <i16> to <i32>
    %1 = constant %arg1 {handshake.name = "constant0", value = 32 : i32} : <>, <i32>
    %2 = shrsi %0, %1 {handshake.name = "shrsi0"} : <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shrsi_zext(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 4 : i16} : <>, <i16>
    %1 = shrui %arg0, %0 {handshake.name = "shrui0"} : <i16>
    %2 = extui %1 {handshake.name = "extui0"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shrsi_large(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 15 : i16} : <>, <i16>
    %1 = shrsi %arg0, %0 {handshake.name = "shrsi0"} : <i16>
    %2 = extsi %1 {handshake.name = "extsi0"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shruiFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 4 : i16} : <>, <i16>
    %1 = shrui %arg0, %0 {handshake.name = "shrui0"} : <i16>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i16> to <i12>
    %3 = extsi %2 {handshake.name = "extsi0"} : <i12> to <i28>
    %4 = extui %3 {handshake.name = "extui0"} : <i28> to <i32>
    end {handshake.name = "end0"} %4 : <i32>
  }
}


// -----
module {
  handshake.func @shrui_edge_case(%arg0: !handshake.channel<i29>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 4 : i29} : <>, <i29>
    %1 = shrui %arg0, %0 {handshake.name = "shrui0"} : <i29>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i29> to <i25>
    %3 = extsi %2 {handshake.name = "extsi0"} : <i25> to <i28>
    %4 = extui %3 {handshake.name = "extui0"} : <i28> to <i32>
    end {handshake.name = "end0"} %4 : <i32>
  }
}


// -----
module {
  handshake.func @shrui_si_overflow(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 15 : i16} : <>, <i16>
    %1 = shrui %arg0, %0 {handshake.name = "shrui0"} : <i16>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i16> to <i1>
    %3 = extsi %2 {handshake.name = "extsi0"} : <i1> to <i14>
    %4 = extui %3 {handshake.name = "extui0"} : <i14> to <i32>
    end {handshake.name = "end0"} %4 : <i32>
  }
}


// -----
module {
  handshake.func @shrui_ui_FW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 4 : i16} : <>, <i16>
    %1 = shrui %arg0, %0 {handshake.name = "shrui0"} : <i16>
    %2 = extui %1 {handshake.name = "extui0"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @shrui_ui_overflowFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    end {handshake.name = "end0"} %0 : <i32>
  }
}


// -----
module {
  handshake.func @cmpiFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i1> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %1 = cmpi eq, %0, %arg1 {handshake.name = "cmpi0"} : <i16>
    end {handshake.name = "end0"} %1 : <i1>
  }
}


// -----
module {
  handshake.func @selectFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.channel<i1>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "select", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %1 = select %arg2[%0, %arg1] {handshake.name = "select0"} : <i1>, <i16>
    %2 = extsi %1 {handshake.name = "extsi1"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @extui_extsi(%arg0: !handshake.channel<i8>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.name = "extui0"} : <i8> to <i32>
    end {handshake.name = "end0"} %0 : <i32>
  }
}


// -----
module {
  handshake.func @extsi_extui(%arg0: !handshake.channel<i8>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.name = "extsi0"} : <i8> to <i16>
    %1 = extui %0 {handshake.name = "extui0"} : <i16> to <i32>
    end {handshake.name = "end0"} %1 : <i32>
  }
}


// -----
module {
  handshake.func @extsi_extsi(%arg0: !handshake.channel<i8>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.name = "extsi0"} : <i8> to <i32>
    end {handshake.name = "end0"} %0 : <i32>
  }
}


// -----
module {
  handshake.func @extui_extui(%arg0: !handshake.channel<i8>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.name = "extui0"} : <i8> to <i32>
    end {handshake.name = "end0"} %0 : <i32>
  }
}


// -----
module {
  handshake.func @mux_cycle(%arg0: !handshake.channel<i16>, %arg1: !handshake.channel<i1>, %arg2: !handshake.control<>, %arg3: !handshake.channel<i1>, ...) -> (!handshake.channel<i8>, !handshake.control<>) attributes {argNames = ["var0", "var1", "start", "bool"], resNames = ["out0", "end"]} {
    %0 = source {handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.name = "constant0", value = 0 : i16} : <>, <i16>
    %2 = cmpi eq, %arg0, %1 {handshake.name = "cmpi0"} : <i16>
    %trueResult, %falseResult = cond_br %2, %2 {handshake.name = "cond_br0"} : <i1>, <i1>
    %3 = br %arg1 {handshake.name = "br0"} : <i1>
    %4 = mux %arg3 [%falseResult, %3] {handshake.name = "mux0"} : <i1>, [<i1>, <i1>] to <i1>
    %5 = extui %4 {handshake.name = "extui0"} : <i1> to <i8>
    end {handshake.name = "end0"} %5, %arg2 : <i8>, <>
  }
}


// -----
module {
  handshake.func @ori_ui_si(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i9>
    %1 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i9>
    %2 = ori %1, %0 {handshake.name = "ori0"} : <i9>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i9> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @cmpi_ui_si1(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i1> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i9>
    %1 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i9>
    %2 = cmpi eq, %1, %0 {handshake.name = "cmpi0"} : <i9>
    end {handshake.name = "end0"} %2 : <i1>
  }
}


// -----
module {
  handshake.func @cmpi_ui_si2(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i1> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i9>
    %1 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i9>
    %2 = cmpi eq, %1, %0 {handshake.name = "cmpi0"} : <i9>
    end {handshake.name = "end0"} %2 : <i1>
  }
}


// -----
module {
  handshake.func @cmpi_sge_ui_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i1> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i9>
    %1 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i8> to <i9>
    %2 = cmpi sge, %1, %0 {handshake.name = "cmpi0"} : <i9>
    end {handshake.name = "end0"} %2 : <i1>
  }
}


// -----
module {
  handshake.func @cmpi_sge_si_si(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i1> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = cmpi sge, %arg1, %arg0 {handshake.name = "cmpi0"} : <i8>
    end {handshake.name = "end0"} %0 : <i1>
  }
}

