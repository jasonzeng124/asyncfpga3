module {
  handshake.func @iir(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["y", "x", "a", "b", "y_start", "x_start", "start"], resNames = ["out0", "y_end", "x_end", "end"]} {
    %0:4 = fork [4] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg5 (%addressResult_2) %34#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg4 (%addressResult, %20, %addressResult_4, %dataResult_5) %34#0 {connectedBlocks = [0 : i32, 1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = 0 : i10} : <>, <i10>
    %addressResult, %dataResult = load[%1] %outputs_0 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %2 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant7", value = true} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %5 = br %dataResult {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %6 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %7 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %8 = br %0#3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %9 = mux %18#0 [%4, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10:3 = fork [3] %9 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %11 = trunci %10#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %12 = trunci %10#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %13 = mux %18#1 [%5, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %18#2 [%6, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %16 = mux %18#3 [%7, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%8, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %18:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %19:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %20 = constant %19#0 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1000 : i32} : <>, <i32>
    %23 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %24 = constant %23 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %25 = muli %13, %15#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %addressResult_2, %dataResult_3 = load[%12] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %26 = muli %dataResult_3, %17#1 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %27 = addi %25, %26 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %28:2 = fork [2] %27 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %addressResult_4, %dataResult_5 = store[%11] %28#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %29 = addi %10#2, %24 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %31 = cmpi ne, %30#1, %22 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %32:5 = fork [5] %31 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult, %falseResult = cond_br %32#4, %30#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %32#3, %28#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %32#2, %15#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink1"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %32#1, %17#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %32#0, %19#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %33 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_15 {handshake.name = "sink3"} : <i1>
    %34:2 = fork [2] %result_14 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %33, %memEnd_1, %memEnd, %0#2 : <i32>, <>, <>, <>
  }
}

