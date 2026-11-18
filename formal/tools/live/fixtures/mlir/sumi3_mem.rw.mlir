module {
  handshake.func @sumi3_mem(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg1 (%addressResult) %result_4 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3:2 = fork [2] %2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i1>
    %4 = extui %3#1 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %5 = extui %3#0 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i10>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = mux %12#0 [%5, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i10>
    %9 = extui %8#1 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i10> to <i11>
    %10 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i11} : <>, <i11>
    %11 = mux %12#1 [%4, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%8#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %15:3 = fork [3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %16 = muli %15#0, %15#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %17 = muli %16, %15#2 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %18 = addi %11, %17 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %19 = addi %9, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i11>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i11>
    %21 = trunci %20#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %22 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1000 : i11} : <>, <i11>
    %23 = cmpi ult, %20#1, %22 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i11>
    %24:3 = fork [3] %23 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %24#0, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i10>
    sink %falseResult {handshake.name = "sink0"} : <i10>
    %trueResult_0, %falseResult_1 = cond_br %24#1, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %24#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %25 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink1"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %25, %memEnd, %0#1 : <i32>, <>, <>
  }
}

