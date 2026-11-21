module {
  handshake.func @test_memory_18(%arg0: memref<4xi32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "y", "x_start", "y_start", "start"], resNames = ["x_end", "y_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<4xi32>] %arg3 (%addressResult_2) %22#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i2>) -> !handshake.channel<i32>
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<4xi32>] %arg2 (%10, %addressResult, %addressResult_4, %addressResult_6, %dataResult_7) %22#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = true} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i2>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %6:4 = fork [4] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i2>
    %7 = extui %6#3 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i2> to <i3>
    %8 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i3} : <>, <i3>
    %result, %index = control_merge [%4, %trueResult_8]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %10 = constant %9#1 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%6#2] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %addressResult_2, %dataResult_3 = load[%6#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %13 = muli %dataResult, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %14 = constant %9#0 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i2} : <>, <i2>
    %addressResult_4, %dataResult_5 = load[%14] %outputs_0#1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i2>, <i32>, <i2>, <i32>
    %15 = addi %13, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %addressResult_6, %dataResult_7 = store[%6#0] %15 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : <i2>, <i32>, <i2>, <i32>
    %16 = addi %7, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i3>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i3>
    %18 = trunci %17#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i3> to <i2>
    %19 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = -4 : i3} : <>, <i3>
    %20 = cmpi ult, %17#1, %19 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i3>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %21#0, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i2>
    sink %falseResult {handshake.name = "sink0"} : <i2>
    %trueResult_8, %falseResult_9 = cond_br %21#1, %9#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_10, %index_11 = control_merge [%falseResult_9]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink1"} : <i1>
    %22:2 = fork [2] %result_10 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %0#1 : <>, <>, <>
  }
}

