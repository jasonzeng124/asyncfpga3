module {
  handshake.func @fold64(%arg0: !handshake.channel<i64>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["v", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 255 : i32} : <>, <i32>
    %2 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %3 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 81985529216486895 : i64} : <>, <i64>
    %4 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i64> to <i32>
    %5 = andi %4, %1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i32>
    %6 = cmpi ugt, %5, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %6, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %6, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i64>
    %trueResult_2, %falseResult_3 = cond_br %6, %3 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i64>
    %trueResult_4, %falseResult_5 = cond_br %6, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %6, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %7 = mux %index [%trueResult, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i64>, <i64>] to <i64>
    %9 = mux %index [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i64>, <i64>] to <i64>
    %10 = mux %index [%trueResult_4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 11 : i64} : <>, <i64>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 3 : i64} : <>, <i64>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 7 : i64} : <>, <i64>
    %19 = shli %9, %18 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i64>
    %20 = xori %8, %19 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i64>
    %21 = addi %9, %20 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i64>
    %22 = cmpi ult, %21, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i64>
    %23 = shrui %8, %16 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i64>
    %24 = addi %21, %23 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i64>
    %25 = select %22[%24, %21] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i64>
    %26 = shrui %8, %14 {handshake.bb = 1 : ui32, handshake.name = "shrui1"} : <i64>
    %27 = xori %8, %26 {handshake.bb = 1 : ui32, handshake.name = "xori1"} : <i64>
    %28 = addi %7, %12 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %29 = cmpi ne, %28, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %29, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %29, %27 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i64>
    %trueResult_12, %falseResult_13 = cond_br %29, %25 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_14, %falseResult_15 = cond_br %29, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %29, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %30 = mux %index_19 [%falseResult_3, %falseResult_13] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_18, %index_19 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 32 : i64} : <>, <i64>
    %33 = shrui %30, %32 {handshake.bb = 2 : ui32, handshake.name = "shrui2"} : <i64>
    %34 = xori %30, %33 {handshake.bb = 2 : ui32, handshake.name = "xori2"} : <i64>
    %35 = trunci %34 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %35, %arg1 : <i32>, <>
  }
}

