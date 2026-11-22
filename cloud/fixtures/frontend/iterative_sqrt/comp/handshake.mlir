module {
  handshake.func @iterative_sqrt(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = cmpi slt, %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %1, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %2 = mux %index [%falseResult, %falseResult_17] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %3 = mux %index [%falseResult_3, %falseResult_21] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%falseResult, %falseResult_23] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_19]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %7 = addi %3, %2 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %8 = shrsi %7, %6 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %9 = muli %8, %8 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %10 = cmpi eq, %9, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %10, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %10, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %10, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %10, %2 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %10, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %11 = merge %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %12 = merge %falseResult_11 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %13 = merge %falseResult_13 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %14 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = -1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %19 = muli %14, %14 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %20 = cmpi slt, %19, %11 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %21 = addi %14, %18 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %22 = addi %14, %16 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %23 = select %20[%21, %13] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %24 = select %20[%12, %22] {handshake.bb = 2 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %25 = cmpi sgt, %23, %24 {handshake.bb = 2 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %25, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %25, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %trueResult_20, %falseResult_21 = cond_br %25, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %25, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %26 = mux %index_25 [%trueResult, %trueResult_4, %trueResult_16] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_24, %index_25 = control_merge [%trueResult_0, %trueResult_6, %trueResult_18]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>, <>] to <>, <i2>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %26, %arg1 : <i32>, <>
  }
}

