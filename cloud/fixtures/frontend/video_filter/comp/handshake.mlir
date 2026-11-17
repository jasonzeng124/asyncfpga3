module {
  handshake.func @video_filter(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: memref<900xi32>, %arg3: memref<900xi32>, %arg4: memref<900xi32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["offset", "scale", "pixelR", "pixelG", "pixelB", "pixelR_start", "pixelG_start", "pixelB_start", "start"], resNames = ["pixelR_end", "pixelG_end", "pixelB_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg4 : memref<900xi32>] %arg7 (%26, %addressResult_8, %addressResult_10, %dataResult_11) %result_46 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg3 : memref<900xi32>] %arg6 (%27, %addressResult_12, %addressResult_14, %dataResult_15) %result_46 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_2, %memEnd_3 = mem_controller[%arg2 : memref<900xi32>] %arg5 (%28, %addressResult, %addressResult_6, %dataResult_7) %result_46 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %2 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %3 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %4 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %5 = mux %index [%1, %trueResult_38] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%2, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%3, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %9 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %11 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %12 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %13 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %14 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %15 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %16 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %17 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %18 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %19 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i64>
    %20 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i64>
    %21 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i64>
    %22 = br %12 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i64>
    %23 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br14"} : <i64>
    %24 = br %14 {handshake.bb = 1 : ui32, handshake.name = "br15"} : <i64>
    %25 = br %result {handshake.bb = 1 : ui32, handshake.name = "br16"} : <>
    %26 = constant %result_4 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %27 = constant %result_4 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %28 = constant %result_4 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %29 = mux %index_5 [%15, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %30 = mux %index_5 [%16, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %index_5 [%17, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %32 = mux %index_5 [%18, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %index_5 [%19, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %34 = mux %index_5 [%20, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %35 = mux %index_5 [%21, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %36 = mux %index_5 [%22, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux10"} : <i1>, [<i64>, <i64>] to <i64>
    %37 = mux %index_5 [%23, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux11"} : <i1>, [<i64>, <i64>] to <i64>
    %38 = mux %index_5 [%24, %trueResult_32] {handshake.bb = 2 : ui32, handshake.name = "mux12"} : <i1>, [<i64>, <i64>] to <i64>
    %result_4, %index_5 = control_merge [%25, %trueResult_34]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %40 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 30 : i32} : <>, <i32>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %42 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %43 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %44 = constant %43 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 4 : i32} : <>, <i32>
    %45 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %46 = constant %45 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 4 : i64} : <>, <i64>
    %47 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %48 = constant %47 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 3 : i64} : <>, <i64>
    %49 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %50 = constant %49 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %51 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %52 = constant %51 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 1 : i64} : <>, <i64>
    %53 = extui %29 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %54 = shli %33, %52 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %55 = shli %33, %50 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %56 = addi %54, %55 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i64>
    %57 = shli %33, %48 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %58 = shli %33, %46 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %59 = addi %57, %58 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i64>
    %60 = addi %56, %59 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i64>
    %61 = addi %60, %53 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %62 = trunci %61 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%62] %outputs_2 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %63 = subi %dataResult, %30 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %64 = muli %63, %31 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %65 = shrsi %64, %44 {handshake.bb = 2 : ui32, handshake.name = "shrsi0"} : <i32>
    %66 = extui %29 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %67 = shli %34, %52 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %68 = shli %34, %50 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %69 = addi %67, %68 {handshake.bb = 2 : ui32, handshake.name = "addi11"} : <i64>
    %70 = shli %34, %48 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %71 = shli %34, %46 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %72 = addi %70, %71 {handshake.bb = 2 : ui32, handshake.name = "addi12"} : <i64>
    %73 = addi %69, %72 {handshake.bb = 2 : ui32, handshake.name = "addi13"} : <i64>
    %74 = addi %73, %66 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %75 = trunci %74 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = store[%75] %65 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %76 = extui %29 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %77 = shli %35, %52 {handshake.bb = 2 : ui32, handshake.name = "shli8"} : <i64>
    %78 = shli %35, %50 {handshake.bb = 2 : ui32, handshake.name = "shli9"} : <i64>
    %79 = addi %77, %78 {handshake.bb = 2 : ui32, handshake.name = "addi14"} : <i64>
    %80 = shli %35, %48 {handshake.bb = 2 : ui32, handshake.name = "shli10"} : <i64>
    %81 = shli %35, %46 {handshake.bb = 2 : ui32, handshake.name = "shli11"} : <i64>
    %82 = addi %80, %81 {handshake.bb = 2 : ui32, handshake.name = "addi15"} : <i64>
    %83 = addi %79, %82 {handshake.bb = 2 : ui32, handshake.name = "addi16"} : <i64>
    %84 = addi %83, %76 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i64>
    %85 = trunci %84 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = load[%85] %outputs {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %86 = subi %dataResult_9, %30 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i32>
    %87 = muli %86, %31 {handshake.bb = 2 : ui32, handshake.name = "muli4"} : <i32>
    %88 = shrsi %87, %44 {handshake.bb = 2 : ui32, handshake.name = "shrsi1"} : <i32>
    %89 = extui %29 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %90 = shli %36, %52 {handshake.bb = 2 : ui32, handshake.name = "shli12"} : <i64>
    %91 = shli %36, %50 {handshake.bb = 2 : ui32, handshake.name = "shli13"} : <i64>
    %92 = addi %90, %91 {handshake.bb = 2 : ui32, handshake.name = "addi17"} : <i64>
    %93 = shli %36, %48 {handshake.bb = 2 : ui32, handshake.name = "shli14"} : <i64>
    %94 = shli %36, %46 {handshake.bb = 2 : ui32, handshake.name = "shli15"} : <i64>
    %95 = addi %93, %94 {handshake.bb = 2 : ui32, handshake.name = "addi18"} : <i64>
    %96 = addi %92, %95 {handshake.bb = 2 : ui32, handshake.name = "addi19"} : <i64>
    %97 = addi %96, %89 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i64>
    %98 = trunci %97 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = store[%98] %88 {handshake.bb = 2 : ui32, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %99 = extui %29 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %100 = shli %37, %52 {handshake.bb = 2 : ui32, handshake.name = "shli16"} : <i64>
    %101 = shli %37, %50 {handshake.bb = 2 : ui32, handshake.name = "shli17"} : <i64>
    %102 = addi %100, %101 {handshake.bb = 2 : ui32, handshake.name = "addi20"} : <i64>
    %103 = shli %37, %48 {handshake.bb = 2 : ui32, handshake.name = "shli18"} : <i64>
    %104 = shli %37, %46 {handshake.bb = 2 : ui32, handshake.name = "shli19"} : <i64>
    %105 = addi %103, %104 {handshake.bb = 2 : ui32, handshake.name = "addi21"} : <i64>
    %106 = addi %102, %105 {handshake.bb = 2 : ui32, handshake.name = "addi22"} : <i64>
    %107 = addi %106, %99 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i64>
    %108 = trunci %107 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%108] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %109 = subi %dataResult_13, %30 {handshake.bb = 2 : ui32, handshake.name = "subi2"} : <i32>
    %110 = muli %109, %31 {handshake.bb = 2 : ui32, handshake.name = "muli7"} : <i32>
    %111 = shrsi %110, %44 {handshake.bb = 2 : ui32, handshake.name = "shrsi2"} : <i32>
    %112 = extui %29 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %113 = shli %38, %52 {handshake.bb = 2 : ui32, handshake.name = "shli20"} : <i64>
    %114 = shli %38, %50 {handshake.bb = 2 : ui32, handshake.name = "shli21"} : <i64>
    %115 = addi %113, %114 {handshake.bb = 2 : ui32, handshake.name = "addi23"} : <i64>
    %116 = shli %38, %48 {handshake.bb = 2 : ui32, handshake.name = "shli22"} : <i64>
    %117 = shli %38, %46 {handshake.bb = 2 : ui32, handshake.name = "shli23"} : <i64>
    %118 = addi %116, %117 {handshake.bb = 2 : ui32, handshake.name = "addi24"} : <i64>
    %119 = addi %115, %118 {handshake.bb = 2 : ui32, handshake.name = "addi25"} : <i64>
    %120 = addi %119, %112 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i64>
    %121 = trunci %120 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = store[%121] %111 {handshake.bb = 2 : ui32, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %122 = addi %29, %42 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i32>
    %123 = cmpi ult, %122, %40 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %123, %122 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %123, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %123, %31 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %123, %32 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %123, %33 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_24, %falseResult_25 = cond_br %123, %34 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i64>
    %trueResult_26, %falseResult_27 = cond_br %123, %35 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i64>
    %trueResult_28, %falseResult_29 = cond_br %123, %36 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_30, %falseResult_31 = cond_br %123, %37 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i64>
    %trueResult_32, %falseResult_33 = cond_br %123, %38 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i64>
    %trueResult_34, %falseResult_35 = cond_br %123, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %124 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %125 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %126 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %result_36, %index_37 = control_merge [%falseResult_35]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %127 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %128 = constant %127 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 30 : i32} : <>, <i32>
    %129 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %130 = constant %129 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %131 = addi %126, %130 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i32>
    %132 = cmpi ult, %131, %128 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_38, %falseResult_39 = cond_br %132, %131 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %132, %124 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %132, %125 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %132, %result_36 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_45]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_3, %memEnd_1, %memEnd, %arg8 : <>, <>, <>, <>
  }
}

