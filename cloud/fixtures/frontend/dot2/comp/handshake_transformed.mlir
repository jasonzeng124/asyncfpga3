module {
  handshake.func @dot2(%arg0: memref<32xi32>, %arg1: memref<32xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "n", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %0:4 = fork [4] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %outputs, %memEnd = mem_controller[%arg1 : memref<32xi32>] %arg4 (%addressResult_6) %32#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<32xi32>] %arg3 (%addressResult) %32#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:3 = fork [3] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %6:2 = fork [2] %trueResult {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i1>
    %7 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %8 = extui %6#1 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %9 = extui %6#0 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i5>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink0"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %10 = mux %17#0 [%9, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %11:3 = fork [3] %10 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i5>
    %12 = extui %11#2 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i5> to <i6>
    %13 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i6} : <>, <i6>
    %14 = mux %17#1 [%8, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %17#2 [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %17:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%11#1] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %addressResult_6, %dataResult_7 = load[%11#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i5>, <i32>, <i5>, <i32>
    %20 = muli %dataResult, %dataResult_7 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %21 = addi %14, %20 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %22 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i6>
    %23:3 = fork [3] %22 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i6>
    %24 = trunci %23#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i6> to <i5>
    %25 = extui %23#2 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i6> to <i32>
    %26 = cmpi slt, %25, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %27 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = -32 : i6} : <>, <i6>
    %28 = cmpi ult, %23#1, %27 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i6>
    %29 = andi %26, %28 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %30:4 = fork [4] %29 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %30#0, %24 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    sink %falseResult_9 {handshake.name = "sink1"} : <i5>
    %trueResult_10, %falseResult_11 = cond_br %30#3, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %30#2, %16#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink2"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %30#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %31 = mux %index_17 [%7, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_16, %index_17 = control_merge [%falseResult_5, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %32:2 = fork [2] %result_16 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %31, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

