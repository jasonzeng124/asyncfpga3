module {
  handshake.func @lfsrfind(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["seed", "key", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 65535 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %3 = andi %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i32>
    %4 = andi %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "andi1"} : <i32>
    %5 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %6 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %7 = br %4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %8 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %9 = mux %index [%5, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%6, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index [%7, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%8, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12 = cmpi eq, %10, %11 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %12, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %12, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %12, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %12, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %13 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %14 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %15 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_6, %index_7 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %16 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 256 : i32} : <>, <i32>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 46080 : i32} : <>, <i32>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %23 = shrui %15, %20 {handshake.bb = 2 : ui32, handshake.name = "shrui0"} : <i32>
    %24 = andi %15, %20 {handshake.bb = 2 : ui32, handshake.name = "andi2"} : <i32>
    %25 = cmpi eq, %24, %22 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %26 = select %25[%22, %18] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %27 = xori %23, %26 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %28 = addi %14, %20 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %29 = cmpi ne, %28, %16 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %29, %28 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %29, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %29, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %29, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %trueResult_16, %falseResult_17 = cond_br %29, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %30 = mux %index_19 [%trueResult, %falseResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%trueResult_0, %falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %30, %arg2 : <i32>, <>
  }
}

