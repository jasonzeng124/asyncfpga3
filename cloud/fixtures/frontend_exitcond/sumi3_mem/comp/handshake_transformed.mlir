module {
  handshake.func @sumi3_mem(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg1 (%addressResult) %result_4 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %4:2 = fork [2] %3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %10#0 [%4#0, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7:2 = fork [2] %6 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %8 = trunci %7#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %9 = mux %10#1 [%4#1, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1000 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%8] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %15:3 = fork [3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %16 = muli %15#0, %15#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %17 = muli %16, %15#2 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %18 = addi %9, %17 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %19 = addi %7#1, %14 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %21 = cmpi ne, %20#1, %12 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %22:3 = fork [3] %21 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %22#2, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %22#1, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %22#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %23 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink1"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %23, %memEnd, %0#1 : <i32>, <>, <>
  }
}

