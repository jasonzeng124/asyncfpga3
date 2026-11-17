module {
  handshake.func @test_flatten_array(%arg0: memref<512xi32>, %arg1: memref<512xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["input", "output", "input_start", "output_start", "start"], resNames = ["input_end", "output_end", "end"]} {
    %memEnd = mem_controller[%arg1 : memref<512xi32>] %arg3 (%30, %addressResult_5, %dataResult_6) %result_39 {connectedBlocks = [3 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg0 : memref<512xi32>] %arg2 (%addressResult) %result_39 {connectedBlocks = [3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %2 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %3 = mux %index [%1, %trueResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_37]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %5 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %6 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %7 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %8 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %9 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %10 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %11 = br %result {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %12 = mux %index_2 [%7, %trueResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %index_2 [%8, %trueResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_2 [%9, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i64>, <i64>] to <i64>
    %15 = mux %index_2 [%10, %trueResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_1, %index_2 = control_merge [%11, %trueResult_31]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %16 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %17 = constant %16 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 7 : i32} : <>, <i32>
    %18 = constant %result_1 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %19 = subi %17, %12 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %20 = extsi %19 {handshake.bb = 2 : ui32, handshake.name = "extsi0"} : <i32> to <i64>
    %21 = extui %12 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %22 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i32>
    %23 = br %13 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i32>
    %24 = br %14 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i64>
    %25 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i64>
    %26 = br %12 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <i32>
    %27 = br %20 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <i64>
    %28 = br %21 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <i64>
    %29 = br %result_1 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <>
    %30 = constant %result_3 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %31 = mux %index_4 [%22, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %32 = mux %index_4 [%23, %trueResult_7] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %index_4 [%24, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %34 = mux %index_4 [%25, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %35 = mux %index_4 [%26, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %36 = mux %index_4 [%27, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i64>, <i64>] to <i64>
    %37 = mux %index_4 [%28, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i64>, <i64>] to <i64>
    %result_3, %index_4 = control_merge [%29, %trueResult_19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %38 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %39 = constant %38 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 16 : i32} : <>, <i32>
    %40 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %41 = constant %40 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %43 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 15 : i32} : <>, <i32>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 7 : i64} : <>, <i64>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %47 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 4 : i64} : <>, <i64>
    %48 = subi %43, %31 {handshake.bb = 3 : ui32, handshake.name = "subi1"} : <i32>
    %49 = extsi %48 {handshake.bb = 3 : ui32, handshake.name = "extsi1"} : <i32> to <i64>
    %50 = shli %33, %45 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %51 = shli %36, %47 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %52 = addi %51, %49 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i64>
    %53 = addi %50, %52 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i64>
    %54 = trunci %53 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%54] %outputs {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %55 = extui %31 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %56 = shli %34, %45 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %57 = shli %37, %47 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %58 = addi %57, %55 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i64>
    %59 = addi %56, %58 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i64>
    %60 = trunci %59 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_5, %dataResult_6 = store[%60] %dataResult {handshake.bb = 3 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %61 = addi %31, %41 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %62 = cmpi ult, %61, %39 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %62, %61 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_7, %falseResult_8 = cond_br %62, %32 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %62, %33 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_11, %falseResult_12 = cond_br %62, %34 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_13, %falseResult_14 = cond_br %62, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_15, %falseResult_16 = cond_br %62, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i64>
    %trueResult_17, %falseResult_18 = cond_br %62, %37 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_19, %falseResult_20 = cond_br %62, %result_3 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %63 = merge %falseResult_8 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %64 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i64>
    %65 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i64>
    %66 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i32>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %67 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %68 = constant %67 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 8 : i32} : <>, <i32>
    %69 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %70 = constant %69 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %71 = addi %66, %70 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %72 = cmpi ult, %71, %68 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_23, %falseResult_24 = cond_br %72, %71 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_25, %falseResult_26 = cond_br %72, %63 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %72, %64 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i64>
    %trueResult_29, %falseResult_30 = cond_br %72, %65 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i64>
    %trueResult_31, %falseResult_32 = cond_br %72, %result_21 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %73 = merge %falseResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %result_33, %index_34 = control_merge [%falseResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %74 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %75 = constant %74 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 4 : i32} : <>, <i32>
    %76 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %77 = constant %76 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %78 = addi %73, %77 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %79 = cmpi ult, %78, %75 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_35, %falseResult_36 = cond_br %79, %78 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_37, %falseResult_38 = cond_br %79, %result_33 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_39, %index_40 = control_merge [%falseResult_38]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_0, %memEnd, %arg4 : <>, <>, <>
  }
}

