module {
  handshake.func @digitsum(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "base", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 10 : i32} : <>, <i32>
    %4 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %5 = cmpi ult, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %6 = select %5[%3, %arg1] {handshake.bb = 0 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %7 = cmpi eq, %arg0, %4 {handshake.bb = 0 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult, %falseResult = cond_br %7, %4 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %7, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %7, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %7, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %8 = mux %index [%falseResult, %falseResult_7] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9 = mux %index [%falseResult_3, %falseResult_11] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%falseResult_5, %falseResult_13] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %13 = divui %9, %10 {handshake.bb = 1 : ui32, handshake.name = "divui0"} : <i32>
    %14 = muli %13, %10 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %15 = subi %9, %14 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %16 = addi %8, %15 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %17 = cmpi eq, %13, %12 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %17, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %trueResult_10, %falseResult_11 = cond_br %17, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %17, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %18 = mux %index_15 [%trueResult, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_0, %trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %18, %arg2 : <i32>, <>
  }
}

