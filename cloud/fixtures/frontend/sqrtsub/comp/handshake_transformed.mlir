module {
  handshake.func @sqrtsub(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:5 = fork [5] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %3 = cmpi slt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %6 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#3, %0#3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink0"} : <i32>
    %8 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = true} : <>, <i1>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %8 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %trueResult_4 {handshake.name = "sink1"} : <i1>
    %9 = extui %falseResult_5 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %10 = mux %14#0 [%falseResult_3, %falseResult_11] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %14#1 [%6, %falseResult_7] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %14#2 [%9, %falseResult_13] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %19 = subi %10, %13#1 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %21 = addi %13#0, %16 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %23 = addi %11, %18 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %24 = cmpi slt, %20#1, %22#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %25:4 = fork [4] %24 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %25#3, %23 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %25#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %trueResult_10, %falseResult_11 = cond_br %25#1, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %trueResult_10 {handshake.name = "sink2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %25#0, %22#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %trueResult_12 {handshake.name = "sink3"} : <i32>
    %26 = mux %index_15 [%7, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_0, %trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_14 {handshake.name = "sink4"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %26, %0#2 : <i32>, <>
  }
}

