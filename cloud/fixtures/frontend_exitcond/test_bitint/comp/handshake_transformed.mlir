module {
  handshake.func @test_bitint(%arg0: memref<10xi16>, %arg1: memref<10xi5>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["arr", "weight", "arr_start", "weight_start", "start"], resNames = ["out0", "arr_end", "weight_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<10xi5>] %arg3 (%addressResult_2) %26#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i4>) -> !handshake.channel<i5>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<10xi16>] %arg2 (%addressResult) %26#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i4>) -> !handshake.channel<i16>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %4:2 = fork [2] %3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %11#0 [%4#0, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %8 = trunci %7#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i4>
    %9 = trunci %7#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i4>
    %10 = mux %11#1 [%4#1, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 10 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%9] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i4>, <i16>, <i4>, <i16>
    %16 = extui %dataResult {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i16> to <i21>
    %addressResult_2, %dataResult_3 = load[%8] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i4>, <i5>, <i4>, <i5>
    %17 = extui %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i5> to <i21>
    %18 = muli %16, %17 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i21>
    %19 = extui %18 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i21> to <i32>
    %20 = addi %10, %19 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %21 = addi %7#2, %15 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %23 = cmpi ne, %22#1, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %24:3 = fork [3] %23 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %24#2, %22#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %24#1, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %24#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %25 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink1"} : <i1>
    %26:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %25, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

