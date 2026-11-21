module {
  handshake.func @quadrec(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "n", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1013904242 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 1779033703 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = -1150833019 : i32} : <>, <i32>
    %4 = cmpi sgt, %arg1, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %4, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %4, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %4, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %4, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %4, %3 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %4, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %4, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %5 = mux %index [%trueResult, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_0, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%trueResult_2, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%trueResult_4, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %9 = mux %index [%trueResult_6, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%trueResult_8, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_10, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 3 : i32} : <>, <i32>
    %15 = xori %8, %9 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %16 = addi %7, %15 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %17 = shrui %6, %14 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i32>
    %18 = addi %16, %17 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %19 = addi %5, %12 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %20 = cmpi slt, %19, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %20, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %20, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %20, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %20, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %20, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %20, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %20, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %21 = mux %index_27 [%falseResult_7, %falseResult_21] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %22 = mux %index_27 [%falseResult_5, %falseResult_19] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %23 = mux %index_27 [%falseResult_3, %falseResult_17] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %24 = mux %index_27 [%falseResult_1, %falseResult_15] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_11, %falseResult_25]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 2 : i32} : <>, <i32>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %31 = shli %22, %28 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %32 = shli %21, %26 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %33 = xori %31, %32 {handshake.bb = 2 : ui32, handshake.name = "xori1"} : <i32>
    %34 = shli %24, %30 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %35 = xori %33, %34 {handshake.bb = 2 : ui32, handshake.name = "xori2"} : <i32>
    %36 = xori %35, %23 {handshake.bb = 2 : ui32, handshake.name = "xori3"} : <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %36, %arg2 : <i32>, <>
  }
}

