module {
  handshake.func @fir(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["di", "idx", "di_start", "idx_start", "start"], resNames = ["out0", "di_end", "idx_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult) %27#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg2 (%addressResult_2) %27#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3:2 = fork [2] %2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i1>
    %4 = extui %3#1 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %5 = extui %3#0 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i10>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = mux %12#0 [%5, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %8:3 = fork [3] %7 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i10>
    %9 = extui %8#2 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i10> to <i11>
    %10 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i11} : <>, <i11>
    %11 = mux %12#1 [%4, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %addressResult, %dataResult = load[%8#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -25 : i10} : <>, <i10>
    %17 = subi %16, %8#0 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i10>
    %addressResult_2, %dataResult_3 = load[%17] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %18 = muli %dataResult, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %19 = addi %11, %18 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %20 = addi %9, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i11>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i11>
    %22 = trunci %21#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %23 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1000 : i11} : <>, <i11>
    %24 = cmpi ult, %21#1, %23 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i11>
    %25:3 = fork [3] %24 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %25#0, %22 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i10>
    sink %falseResult {handshake.name = "sink0"} : <i10>
    %trueResult_4, %falseResult_5 = cond_br %25#1, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %25#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %26 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink1"} : <i1>
    %27:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %26, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

