module {
  handshake.func @cmpchain(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "y", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = 268435456 : i32} : <>, <i32>
    %1 = cmpi eq, %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %1, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %1, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %2 = merge %falseResult_1 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %3 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %result, %index = control_merge [%falseResult_5]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 536870912 : i32} : <>, <i32>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = -1 : i32} : <>, <i32>
    %7 = andi %2, %3 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %8 = cmpi sgt, %7, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %8, %2 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %8, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %8, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %trueResult_12, %falseResult_13 = cond_br %8, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %9 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %10 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_14, %index_15 = control_merge [%trueResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %11 = constant %result_14 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 805306368 : i32} : <>, <i32>
    %12 = cmpi slt, %9, %10 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %12, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %12, %9 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %12, %10 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %12, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %13 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %14 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %15 = constant %result_24 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1073741824 : i32} : <>, <i32>
    %16 = cmpi ugt, %13, %14 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %16, %15 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %16, %13 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %16, %14 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %16, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %17 = merge %falseResult_29 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i32>
    %18 = merge %falseResult_31 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <i32>
    %result_34, %index_35 = control_merge [%falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %19 = source {handshake.bb = 4 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 1342177280 : i32} : <>, <i32>
    %21 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 1879048192 : i32} : <>, <i32>
    %23 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 1610612736 : i32} : <>, <i32>
    %25 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 256 : i32} : <>, <i32>
    %27 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %28 = constant %27 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 999999 : i32} : <>, <i32>
    %29 = cmpi sgt, %17, %28 {handshake.bb = 4 : ui32, handshake.name = "cmpi4"} : <i32>
    %30 = cmpi ult, %17, %26 {handshake.bb = 4 : ui32, handshake.name = "cmpi5"} : <i32>
    %31 = select %30[%24, %22] {handshake.bb = 4 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %32 = select %29[%20, %31] {handshake.bb = 4 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %33 = br %32 {handshake.bb = 4 : ui32, handshake.name = "br1"} : <i32>
    %34 = br %17 {handshake.bb = 4 : ui32, handshake.name = "br2"} : <i32>
    %35 = br %18 {handshake.bb = 4 : ui32, handshake.name = "br3"} : <i32>
    %36 = br %result_34 {handshake.bb = 4 : ui32, handshake.name = "br4"} : <>
    %37 = mux %index_37 [%trueResult, %falseResult_13, %trueResult_16, %trueResult_26, %33] {handshake.bb = 5 : ui32, handshake.name = "mux0"} : <i3>, [<i32>, <i32>, <i32>, <i32>, <i32>] to <i32>
    %38 = mux %index_37 [%trueResult_0, %falseResult_7, %trueResult_18, %trueResult_28, %34] {handshake.bb = 5 : ui32, handshake.name = "mux1"} : <i3>, [<i32>, <i32>, <i32>, <i32>, <i32>] to <i32>
    %39 = mux %index_37 [%trueResult_2, %falseResult_9, %trueResult_20, %trueResult_30, %35] {handshake.bb = 5 : ui32, handshake.name = "mux2"} : <i3>, [<i32>, <i32>, <i32>, <i32>, <i32>] to <i32>
    %result_36, %index_37 = control_merge [%trueResult_4, %falseResult_11, %trueResult_22, %trueResult_32, %36]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>, <>, <>, <>] to <>, <i3>
    %40 = subi %38, %39 {handshake.bb = 5 : ui32, handshake.name = "subi0"} : <i32>
    %41 = xori %37, %40 {handshake.bb = 5 : ui32, handshake.name = "xori0"} : <i32>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %41, %arg2 : <i32>, <>
  }
}

