module {
  handshake.func @nested(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_36] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_38] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_2, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_4, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %8 = cmpi sgt, %6, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %8, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %8, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %8, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %8, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %8, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %8, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %9 = mux %index_21 [%trueResult_8, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index_21 [%trueResult_10, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index_21 [%trueResult_12, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %index_21 [%trueResult_14, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %index_21 [%trueResult_16, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%trueResult_18, %trueResult_32]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 3 : i32} : <>, <i32>
    %16 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %17 = constant %16 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %18 = shli %10, %15 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %19 = xori %10, %18 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %20 = addi %19, %13 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %21 = addi %20, %9 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %22 = addi %9, %17 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %23 = cmpi ne, %22, %12 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %23, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %23, %21 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %23, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %23, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %23, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %23, %result_20 {handshake.bb = 2 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %24 = mux %index_35 [%falseResult_11, %falseResult_25] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %index_35 [%falseResult_13, %falseResult_27] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_35 [%falseResult_15, %falseResult_29] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_35 [%falseResult_17, %falseResult_31] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_34, %index_35 = control_merge [%falseResult_19, %falseResult_33]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %28 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %29 = constant %28 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %30 = addi %27, %29 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %31 = cmpi ne, %30, %25 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_36, %falseResult_37 = cond_br %31, %30 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_38, %falseResult_39 = cond_br %31, %24 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %31, %25 {handshake.bb = 3 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %31, %26 {handshake.bb = 3 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %31, %result_34 {handshake.bb = 3 : ui32, handshake.name = "cond_br25"} : <i1>, <>
    %32 = mux %index_47 [%falseResult_1, %falseResult_39] {handshake.bb = 4 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %result_46, %index_47 = control_merge [%falseResult_7, %falseResult_45]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %32, %arg2 : <i32>, <>
  }
}

