module {
  handshake.func @single_loop(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "c_start", "start"], resNames = ["a_end", "b_end", "c_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%11, %addressResult_5, %dataResult_6) %21#2 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<1000xi32>] %arg4 (%addressResult_3) %21#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult) %21#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6:4 = fork [4] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %7 = trunci %6#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %8 = trunci %6#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %9 = trunci %6#2 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %result, %index = control_merge [%4, %trueResult_7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %11 = constant %10#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1000 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%9] %outputs_1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_3, %dataResult_4 = load[%8] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %16 = muli %dataResult, %dataResult_4 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %addressResult_5, %dataResult_6 = store[%7] %17#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %18 = cmpi slt, %17#1, %15 {dynamatic.speculate = {max_predictions = 7 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %20 = addi %6#3, %13 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult, %falseResult = cond_br %19#1, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_7, %falseResult_8 = cond_br %19#0, %10#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_9, %index_10 = control_merge [%falseResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_10 {handshake.name = "sink1"} : <i1>
    %21:3 = fork [3] %result_9 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

