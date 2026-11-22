module {
  handshake.func @twoloops(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "n", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = cmpi sgt, %arg1, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %1, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %1, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %2 = mux %index [%trueResult, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %3 = mux %index [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 7 : i32} : <>, <i32>
    %9 = shli %2, %8 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %10 = xori %2, %9 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %11 = addi %10, %3 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %12 = addi %3, %6 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %13 = cmpi slt, %12, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %13, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %13, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %13, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %13, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %14 = mux %index_15 [%falseResult, %falseResult_7] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 255 : i32} : <>, <i32>
    %17 = constant %result_14 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %18 = andi %14, %16 {handshake.bb = 2 : ui32, handshake.name = "andi0"} : <i32>
    %19 = cmpi ugt, %18, %17 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %19, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %19, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %19, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %19, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %20 = mux %index_25 [%trueResult_16, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %21 = mux %index_25 [%trueResult_18, %trueResult_28] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %22 = mux %index_25 [%trueResult_20, %trueResult_30] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_24, %index_25 = control_merge [%trueResult_22, %trueResult_32]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %23 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 40503 : i32} : <>, <i32>
    %25 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %27 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %28 = constant %27 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %29 = shrui %21, %26 {handshake.bb = 3 : ui32, handshake.name = "shrui0"} : <i32>
    %30 = xori %21, %29 {handshake.bb = 3 : ui32, handshake.name = "xori1"} : <i32>
    %31 = addi %30, %24 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %32 = addi %20, %28 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %33 = cmpi ult, %32, %22 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %33, %32 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %33, %31 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %33, %22 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %33, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %34 = mux %index_35 [%falseResult_19, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_34, %index_35 = control_merge [%falseResult_23, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %34, %arg2 : <i32>, <>
  }
}

