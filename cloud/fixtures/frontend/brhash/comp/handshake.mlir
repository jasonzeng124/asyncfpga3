module {
  handshake.func @brhash(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "n", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = cmpi sgt, %arg1, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %1, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %1, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %2 = mux %index [%trueResult, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %3 = mux %index [%trueResult_0, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_2, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_26]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %9 = andi %3, %6 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %10 = cmpi eq, %9, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %10, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %10, %2 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %10, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %10, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %11 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %12 = merge %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %13 = merge %falseResult_11 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 13 : i32} : <>, <i32>
    %16 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %17 = constant %16 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = -306674912 : i32} : <>, <i32>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 4 : i32} : <>, <i32>
    %22 = shrui %13, %19 {handshake.bb = 2 : ui32, handshake.name = "shrui0"} : <i32>
    %23 = xori %22, %17 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %24 = shli %23, %21 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i32>
    %25 = addi %23, %24 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %26 = addi %25, %12 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %27 = shrui %26, %15 {handshake.bb = 2 : ui32, handshake.name = "shrui1"} : <i32>
    %28 = xori %26, %27 {handshake.bb = 2 : ui32, handshake.name = "xori1"} : <i32>
    %29 = br %28 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %30 = br %11 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <i32>
    %31 = br %12 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %32 = br %result_14 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %33 = merge %trueResult_6 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %34 = merge %trueResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %35 = merge %trueResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %result_16, %index_17 = control_merge [%trueResult_12]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %36 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %37 = constant %36 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 625341585 : i32} : <>, <i32>
    %38 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %39 = constant %38 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 5 : i32} : <>, <i32>
    %40 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %41 = constant %40 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 2 : i32} : <>, <i32>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source9"} : <>
    %43 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 9 : i32} : <>, <i32>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source10"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %46 = shli %35, %43 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i32>
    %47 = xori %35, %46 {handshake.bb = 3 : ui32, handshake.name = "xori2"} : <i32>
    %48 = shrui %47, %41 {handshake.bb = 3 : ui32, handshake.name = "shrui2"} : <i32>
    %49 = shli %34, %45 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i32>
    %50 = addi %48, %49 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %51 = shli %50, %39 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i32>
    %52 = xori %50, %51 {handshake.bb = 3 : ui32, handshake.name = "xori3"} : <i32>
    %53 = xori %52, %37 {handshake.bb = 3 : ui32, handshake.name = "xori4"} : <i32>
    %54 = br %53 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i32>
    %55 = br %33 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <i32>
    %56 = br %34 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <i32>
    %57 = br %result_16 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <>
    %58 = mux %index_19 [%29, %54] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %59 = mux %index_19 [%30, %55] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %60 = mux %index_19 [%31, %56] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%32, %57]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %61 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %62 = constant %61 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 1 : i32} : <>, <i32>
    %63 = addi %60, %62 {handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i32>
    %64 = cmpi slt, %63, %59 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %64, %63 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %64, %58 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %64, %59 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %64, %result_18 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %65 = mux %index_29 [%falseResult_1, %falseResult_23] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_28, %index_29 = control_merge [%falseResult_5, %falseResult_27]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %65, %arg2 : <i32>, <>
  }
}

