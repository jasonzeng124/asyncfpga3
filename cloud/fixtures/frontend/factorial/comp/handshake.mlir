module {
  handshake.func @factorial(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %2 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %3 = cmpi sgt, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %4 = mux %index [%falseResult_1, %falseResult_15] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%falseResult, %falseResult_13] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_3, %falseResult_17]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %8 = cmpi sgt, %5, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %8, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %8, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %8, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %9 = mux %index_11 [%trueResult, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index_11 [%trueResult_0, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%trueResult_2, %trueResult_16]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %12 = constant %11 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = -3 : i32} : <>, <i32>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = -2 : i32} : <>, <i32>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = -1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 2 : i32} : <>, <i32>
    %19 = addi %9, %16 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %20 = muli %9, %19 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %21 = addi %9, %14 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %22 = muli %20, %21 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %23 = muli %10, %22 {handshake.bb = 2 : ui32, handshake.name = "muli2"} : <i32>
    %24 = addi %9, %12 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %25 = cmpi sgt, %24, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %25, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %25, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %25, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %26 = mux %index_19 [%trueResult_4, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_19 [%trueResult_6, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%trueResult_8, %trueResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %28 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %29 = constant %28 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = -1 : i32} : <>, <i32>
    %30 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %31 = constant %30 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %32 = muli %27, %26 {handshake.bb = 3 : ui32, handshake.name = "muli3"} : <i32>
    %33 = addi %26, %29 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %34 = cmpi sgt, %33, %31 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %34, %33 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %34, %32 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %34, %result_18 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %35 = mux %index_27 [%falseResult_7, %falseResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_9, %falseResult_25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %35, %arg1 : <i32>, <>
  }
}

