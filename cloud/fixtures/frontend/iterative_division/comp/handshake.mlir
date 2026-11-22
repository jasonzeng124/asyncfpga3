module {
  handshake.func @iterative_division(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["dividend", "divisor", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = -1 : i32} : <>, <i32>
    %3 = cmpi eq, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %4 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %5 = merge %falseResult_5 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %result, %index = control_merge [%falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -1 : i32} : <>, <i32>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %9 = cmpi sgt, %4, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %10 = subi %8, %4 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %11 = select %9[%4, %10] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %12 = cmpi sgt, %5, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %13 = subi %8, %5 {handshake.bb = 1 : ui32, handshake.name = "subi1"} : <i32>
    %14 = select %12[%5, %13] {handshake.bb = 1 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %15 = cmpi slt, %11, %14 {handshake.bb = 1 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %15, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %15, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %15, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %15, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %trueResult_14, %falseResult_15 = cond_br %15, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %15, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %16 = mux %index_19 [%falseResult_15, %falseResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_19 [%falseResult_7, %falseResult_21] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_19 [%falseResult_9, %falseResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %index_19 [%falseResult_11, %falseResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %20 = mux %index_19 [%falseResult_17, %falseResult_31] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%falseResult_13, %falseResult_27]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %23 = subi %16, %20 {handshake.bb = 2 : ui32, handshake.name = "subi2"} : <i32>
    %24 = addi %17, %22 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %25 = cmpi slt, %23, %20 {handshake.bb = 2 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %25, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %25, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %25, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %25, %result_18 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %trueResult_28, %falseResult_29 = cond_br %25, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %25, %20 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %26 = mux %index_33 [%trueResult_6, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_33 [%trueResult_8, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %28 = mux %index_33 [%trueResult_10, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%trueResult_12, %trueResult_26]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %29 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %30 = constant %29 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %31 = xori %27, %28 {handshake.bb = 3 : ui32, handshake.name = "xori0"} : <i32>
    %32 = cmpi slt, %31, %30 {handshake.bb = 3 : ui32, handshake.name = "cmpi5"} : <i32>
    %33 = subi %30, %26 {handshake.bb = 3 : ui32, handshake.name = "subi3"} : <i32>
    %34 = select %32[%33, %26] {handshake.bb = 3 : ui32, handshake.name = "select2"} : <i1>, <i32>
    %35 = br %34 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <i32>
    %36 = br %result_32 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <>
    %37 = mux %index_35 [%trueResult, %35] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_34, %index_35 = control_merge [%trueResult_0, %36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %37, %arg2 : <i32>, <>
  }
}

