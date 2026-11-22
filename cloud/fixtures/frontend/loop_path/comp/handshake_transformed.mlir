module {
  handshake.func @loop_path(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "c_start", "start"], resNames = ["a_end", "b_end", "c_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%11, %addressResult_5, %dataResult_6) %30#2 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<1000xi32>] %arg4 (%addressResult_3) %30#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult) %30#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6:5 = fork [5] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %7 = trunci %6#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %8 = trunci %6#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %9 = trunci %6#2 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %result, %index = control_merge [%4, %trueResult_7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %11 = constant %10#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 999 : i32} : <>, <i32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 1000 : i32} : <>, <i32>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %19 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%9] %outputs_1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_3, %dataResult_4 = load[%8] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %20 = addi %dataResult, %dataResult_4 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %21:4 = fork [4] %20 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %addressResult_5, %dataResult_6 = store[%7] %21#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %22 = subi %17, %21#3 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %23 = shli %21#2, %19 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %24 = addi %21#1, %23 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %25 = cmpi sgt, %22, %24 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %26 = cmpi ult, %6#4, %15 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %27 = andi %25, %26 {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %28:2 = fork [2] %27 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %29 = addi %6#3, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %trueResult, %falseResult = cond_br %28#1, %29 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_7, %falseResult_8 = cond_br %28#0, %10#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_9, %index_10 = control_merge [%falseResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_10 {handshake.name = "sink1"} : <i1>
    %30:3 = fork [3] %result_9 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

