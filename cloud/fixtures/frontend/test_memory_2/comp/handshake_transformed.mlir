module {
  handshake.func @test_memory_2(%arg0: memref<5xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<5xi32>] %arg2 (%19, %addressResult, %addressResult_4, %dataResult_5) %result_12 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i3>, !handshake.channel<i3>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %4 = addi %arg1, %2 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %5:2 = fork [2] %4 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %6 = cmpi sgt, %5#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %7:3 = fork [3] %6 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %8 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %7#0, %8 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %9 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %7#2, %5#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %7#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %10 = mux %17#0 [%9, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %11:3 = fork [3] %10 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %12 = trunci %11#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i3>
    %13 = constant %23#0 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i3} : <>, <i3>
    %14 = trunci %11#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i3>
    %15 = mux %17#1 [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %17:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %18:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <>
    %19 = constant %18#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %21 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 5 : i32} : <>, <i32>
    %22 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %23:2 = fork [2] %22 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <>
    %24 = constant %23#1 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %25 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i3>
    %addressResult, %dataResult = load[%25] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i3>, <i32>, <i3>, <i32>
    %26 = addi %dataResult, %21 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %addressResult_4, %dataResult_5 = store[%14] %26 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i3>, <i32>, <i3>, <i32>
    %27 = addi %11#2, %24 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %28:2 = fork [2] %27 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %29 = cmpi slt, %28#1, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %30:3 = fork [3] %29 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %30#2, %28#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %30#1, %16#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %30#0, %18#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_12, %index_13 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_13 {handshake.name = "sink4"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %0#1 : <>, <>
  }
}

