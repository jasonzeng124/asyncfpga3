module {
  handshake.func @digitdiv(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "base", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i32>
    %3 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %4 = constant %3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %5 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 10 : i32} : <>, <i32>
    %7 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %8 = cmpi ult, %1#1, %4 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %9 = select %8[%6, %1#0] {handshake.bb = 0 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %10 = cmpi eq, %2#1, %7 {handshake.bb = 0 : ui32, handshake.name = "cmpi1"} : <i32>
    %11:4 = fork [4] %10 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i1>
    %12 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %11#0, %12 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %13 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %14 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %11#3, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %11#2, %2#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink0"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %11#1, %9 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %trueResult_4 {handshake.name = "sink1"} : <i32>
    %15 = mux %20#0 [%13, %falseResult_7] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %20#1 [%falseResult_3, %falseResult_11] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %18 = mux %20#2 [%falseResult_5, %falseResult_13] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %19:3 = fork [3] %18 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %20:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %23 = divui %17#1, %19#2 {handshake.bb = 1 : ui32, handshake.name = "divui0"} : <i32>
    %24:3 = fork [3] %23 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %25 = muli %24#2, %19#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %26 = subi %17#0, %25 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %27 = addi %15, %26 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %28 = cmpi eq, %24#1, %22 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %29:4 = fork [4] %28 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %29#3, %27 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %29#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %trueResult_10, %falseResult_11 = cond_br %29#1, %24#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %trueResult_10 {handshake.name = "sink2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %29#0, %19#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %trueResult_12 {handshake.name = "sink3"} : <i32>
    %30 = mux %index_15 [%14, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_0, %trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_14 {handshake.name = "sink4"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %30, %0#1 : <i32>, <>
  }
}

