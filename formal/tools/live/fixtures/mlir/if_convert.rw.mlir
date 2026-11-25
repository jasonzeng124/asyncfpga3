module {
  handshake.func @if_convert(%arg0: memref<200xi32>, %arg1: memref<200xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg1 : memref<200xi32>] %arg3 (%9, %addressResult_1, %dataResult_2) %26#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i8>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg0 : memref<200xi32>] %arg2 (%addressResult) %26#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i8>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = true} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6:4 = fork [4] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %7 = trunci %6#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i8>
    %result, %index = control_merge [%4, %trueResult_3]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %9 = constant %8#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 198 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 10000 : i32} : <>, <i32>
    %14 = constant %8#2 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %15:3 = fork [3] %14 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %addressResult, %dataResult = load[%7] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i8>, <i32>, <i8>, <i32>
    %16 = muli %6#3, %dataResult {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %17 = cmpi slt, %16, %13 {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %18 = addi %6#2, %15#2 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %19 = select %17[%18, %6#1] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %21 = addi %20#1, %15#1 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %23 = trunci %22#0 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i8>
    %addressResult_1, %dataResult_2 = store[%23] %15#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i8>, <i32>, <i8>, <i32>
    %24 = cmpi slt, %20#0, %11 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %25:2 = fork [2] %24 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %25#1, %22#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_3, %falseResult_4 = cond_br %25#0, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_5, %index_6 = control_merge [%falseResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_6 {handshake.name = "sink1"} : <i1>
    %26:2 = fork [2] %result_5 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_0, %memEnd, %0#1 : <>, <>, <>
  }
}

