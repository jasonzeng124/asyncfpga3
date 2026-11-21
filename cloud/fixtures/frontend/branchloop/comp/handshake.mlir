module {
  handshake.func @branchloop(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %4 = mux %index [%trueResult, %trueResult_32] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_0, %trueResult_34] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_36]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %10 = andi %4, %9 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %11 = cmpi eq, %10, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %11, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %11, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %11, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %12 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %13 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_9]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 3 : i32} : <>, <i32>
    %16 = andi %12, %15 {handshake.bb = 2 : ui32, handshake.name = "andi1"} : <i32>
    %17 = cmpi eq, %16, %15 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %17, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %17, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %17, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %18 = mux %index_19 [%trueResult_12, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %index_19 [%trueResult_14, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%trueResult_16, %trueResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %20 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %21 = constant %20 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 3 : i32} : <>, <i32>
    %22 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %23 = constant %22 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %24 = shrsi %18, %23 {handshake.bb = 3 : ui32, handshake.name = "shrsi0"} : <i32>
    %25 = addi %19, %23 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %26 = andi %24, %21 {handshake.bb = 3 : ui32, handshake.name = "andi2"} : <i32>
    %27 = cmpi eq, %26, %21 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %27, %24 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %27, %25 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %27, %result_18 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %28 = mux %index_27 [%falseResult_15, %falseResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %29 = mux %index_27 [%falseResult_13, %falseResult_21] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_17, %falseResult_25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %30 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %31 = constant %30 {handshake.bb = 4 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %32 = addi %29, %31 {handshake.bb = 4 : ui32, handshake.name = "addi1"} : <i32>
    %33 = br %28 {handshake.bb = 4 : ui32, handshake.name = "br2"} : <i32>
    %34 = br %32 {handshake.bb = 4 : ui32, handshake.name = "br3"} : <i32>
    %35 = br %result_26 {handshake.bb = 4 : ui32, handshake.name = "br4"} : <>
    %36 = merge %trueResult_4 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %37 = merge %trueResult_6 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %result_28, %index_29 = control_merge [%trueResult_8]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %38 = source {handshake.bb = 5 : ui32, handshake.name = "source7"} : <>
    %39 = constant %38 {handshake.bb = 5 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %40 = shrsi %36, %39 {handshake.bb = 5 : ui32, handshake.name = "shrsi1"} : <i32>
    %41 = br %37 {handshake.bb = 5 : ui32, handshake.name = "br5"} : <i32>
    %42 = br %40 {handshake.bb = 5 : ui32, handshake.name = "br6"} : <i32>
    %43 = br %result_28 {handshake.bb = 5 : ui32, handshake.name = "br7"} : <>
    %44 = mux %index_31 [%33, %41] {handshake.bb = 6 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %45 = mux %index_31 [%34, %42] {handshake.bb = 6 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_30, %index_31 = control_merge [%35, %43]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %46 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %47 = constant %46 {handshake.bb = 6 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %48 = addi %44, %47 {handshake.bb = 6 : ui32, handshake.name = "addi2"} : <i32>
    %49 = cmpi sgt, %45, %47 {handshake.bb = 6 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_32, %falseResult_33 = cond_br %49, %45 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %49, %48 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %49, %result_30 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %50 = mux %index_39 [%falseResult_1, %falseResult_35] {handshake.bb = 7 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_38, %index_39 = control_merge [%falseResult_3, %falseResult_37]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %50, %arg1 : <i32>, <>
  }
}

