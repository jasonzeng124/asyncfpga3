module {
  handshake.func @image_resize(%arg0: memref<900xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<900xi32>] %arg2 (%15, %addressResult, %addressResult_2, %dataResult_3) %result_22 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %2 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %3 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %4 = mux %index [%1, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%2, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_20]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %7 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %8 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %10 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %11 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %12 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %13 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i64>
    %14 = br %result {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %15 = constant %result_0 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %16 = mux %index_1 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_1 [%10, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_1 [%11, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %index_1 [%12, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i64>, <i64>] to <i64>
    %20 = mux %index_1 [%13, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i64>, <i64>] to <i64>
    %result_0, %index_1 = control_merge [%14, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 30 : i32} : <>, <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %33 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %34 = shli %19, %32 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %35 = shli %19, %30 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %36 = addi %34, %35 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i64>
    %37 = shli %19, %28 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %38 = shli %19, %26 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %39 = addi %37, %38 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i64>
    %40 = addi %36, %39 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %41 = addi %40, %33 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %42 = trunci %41 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%42] %outputs {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %43 = subi %17, %dataResult {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %44 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %45 = shli %20, %32 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %46 = shli %20, %30 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %47 = addi %45, %46 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %48 = shli %20, %28 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %49 = shli %20, %26 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %50 = addi %48, %49 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i64>
    %51 = addi %47, %50 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i64>
    %52 = addi %51, %44 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %53 = trunci %52 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = store[%53] %43 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %54 = addi %16, %24 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %55 = cmpi ne, %54, %22 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %55, %54 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %55, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %55, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %55, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_10, %falseResult_11 = cond_br %55, %20 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_12, %falseResult_13 = cond_br %55, %result_0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %56 = merge %falseResult_5 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %57 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %58 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %59 = constant %58 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 30 : i32} : <>, <i32>
    %60 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %61 = constant %60 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %62 = addi %57, %61 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %63 = cmpi ne, %62, %59 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %63, %62 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %63, %56 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %63, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd, %arg3 : <>, <>
  }
}

