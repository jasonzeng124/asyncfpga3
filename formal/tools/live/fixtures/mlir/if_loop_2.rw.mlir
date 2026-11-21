module {
  handshake.func @if_loop_2(%arg0: memref<100xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %outputs, %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg2 (%addressResult) %result_12 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:3 = fork [3] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %6 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %8:2 = fork [2] %7 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %9 = mux %16#0 [%8#0, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %11 = trunci %10#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %12 = mux %16#1 [%8#1, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %14 = mux %16#2 [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %16:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 10 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%11] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %21:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %22 = cmpi sgt, %21#0, %20 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %23 = addi %13#1, %21#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %24 = select %22[%23, %13#0] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %25 = addi %10#1, %18 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %26:2 = fork [2] %25 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %27 = cmpi slt, %26#1, %15#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %28:4 = fork [4] %27 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %28#3, %26#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %28#2, %24 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %28#1, %15#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink2"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %28#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %29 = mux %index_13 [%6, %falseResult_7] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_12, %index_13 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %29, %memEnd, %0#1 : <i32>, <>, <>
  }
}

