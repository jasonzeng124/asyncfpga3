module {
  handshake.func @collatz(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %3 = cmpi eq, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %4 = mux %index [%falseResult_3, %falseResult_9] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%falseResult, %falseResult_5] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %10 = andi %4, %9 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %11 = cmpi eq, %10, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %12 = shrsi %4, %9 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %13 = shli %4, %9 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %14 = addi %4, %13 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %15 = addi %14, %9 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %16 = select %11[%12, %15] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %17 = addi %5, %9 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %18 = cmpi eq, %16, %9 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %18, %17 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %18, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %18, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %19 = mux %index_11 [%trueResult, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%trueResult_0, %trueResult_6]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %19, %arg1 : <i32>, <>
  }
}

