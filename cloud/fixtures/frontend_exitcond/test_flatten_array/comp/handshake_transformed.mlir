module {
  handshake.func @test_flatten_array(%arg0: memref<512xi32>, %arg1: memref<512xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["input", "output", "input_start", "output_start", "start"], resNames = ["input_end", "output_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg1 : memref<512xi32>] %arg3 (%55, %addressResult_5, %dataResult_6) %106#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i9>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg0 : memref<512xi32>] %arg2 (%addressResult) %106#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i9>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%3, %trueResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6:3 = fork [3] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %result, %index = control_merge [%4, %trueResult_37]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %9 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %10 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %11 = br %6#2 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %12 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %13 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %14 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %15 = mux %20#2 [%10, %trueResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %16:3 = fork [3] %15 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i32>
    %17 = mux %20#3 [%11, %trueResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %20#0 [%12, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %20#1 [%13, %trueResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_1, %index_2 = control_merge [%14, %trueResult_31]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %20:4 = fork [4] %index_2 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i1>
    %21:2 = fork [2] %result_1 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 7 : i32} : <>, <i32>
    %24 = subi %23, %16#2 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %25 = constant %21#0 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %26 = br %25 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i1>
    %27 = extui %26 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i1> to <i32>
    %28 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i32>
    %29 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i32>
    %30 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i32>
    %31 = br %16#1 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <i32>
    %32 = br %24 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <i32>
    %33 = br %16#0 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <i32>
    %34 = br %21#1 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <>
    %35 = mux %53#4 [%27, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %36:3 = fork [3] %35 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i32>
    %37 = trunci %36#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i32> to <i9>
    %38 = trunci %36#1 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i32> to <i9>
    %39 = mux %53#5 [%28, %trueResult_7] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %40 = mux %53#0 [%29, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %41:2 = fork [2] %40 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i32>
    %42 = extui %41#1 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %43 = mux %53#1 [%30, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %44:2 = fork [2] %43 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i32>
    %45 = extui %44#1 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %46 = mux %53#6 [%31, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %47 = mux %53#2 [%32, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %49 = extsi %48#1 {handshake.bb = 3 : ui32, handshake.name = "extsi2"} : <i32> to <i64>
    %50 = mux %53#3 [%33, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %51:2 = fork [2] %50 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %52 = extui %51#1 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %result_3, %index_4 = control_merge [%34, %trueResult_19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %53:7 = fork [7] %index_4 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %54:2 = fork [2] %result_3 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    %55 = constant %54#0 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %56 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %57 = constant %56 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 16 : i32} : <>, <i32>
    %58 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %59 = constant %58 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %60 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %61 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %62 = constant %61 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 7 : i64} : <>, <i64>
    %63:2 = fork [2] %62 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i64>
    %64 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %65 = constant %64 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 4 : i64} : <>, <i64>
    %66:2 = fork [2] %65 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i64>
    %67 = constant %60 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 15 : i9} : <>, <i9>
    %68 = subi %67, %37 {handshake.bb = 3 : ui32, handshake.name = "subi1"} : <i9>
    %69 = shli %42, %63#1 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %70 = trunci %69 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i64> to <i9>
    %71 = shli %49, %66#1 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %72 = trunci %71 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i64> to <i9>
    %73 = addi %72, %68 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i9>
    %74 = addi %70, %73 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i9>
    %addressResult, %dataResult = load[%74] %outputs {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i9>, <i32>, <i9>, <i32>
    %75 = shli %45, %63#0 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %76 = trunci %75 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i64> to <i9>
    %77 = shli %52, %66#0 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %78 = trunci %77 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i64> to <i9>
    %79 = addi %78, %38 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i9>
    %80 = addi %76, %79 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i9>
    %addressResult_5, %dataResult_6 = store[%80] %dataResult {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i9>, <i32>, <i9>, <i32>
    %81 = addi %36#2, %59 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %82:2 = fork [2] %81 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i32>
    %83 = cmpi ne, %82#1, %57 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %84:8 = fork [8] %83 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult, %falseResult = cond_br %84#7, %82#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_7, %falseResult_8 = cond_br %84#6, %39 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %84#0, %41#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %84#1, %44#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %84#5, %46 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_15, %falseResult_16 = cond_br %84#2, %48#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_16 {handshake.name = "sink1"} : <i32>
    %trueResult_17, %falseResult_18 = cond_br %84#3, %51#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_18 {handshake.name = "sink2"} : <i32>
    %trueResult_19, %falseResult_20 = cond_br %84#4, %54#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %85 = merge %falseResult_8 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %86 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i32>
    %87 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %88 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i32>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink3"} : <i1>
    %89 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %90 = constant %89 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 8 : i32} : <>, <i32>
    %91 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %92 = constant %91 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %93 = addi %88, %92 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %94:2 = fork [2] %93 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i32>
    %95 = cmpi ne, %94#1, %90 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %96:5 = fork [5] %95 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_23, %falseResult_24 = cond_br %96#4, %94#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_24 {handshake.name = "sink4"} : <i32>
    %trueResult_25, %falseResult_26 = cond_br %96#3, %85 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %96#0, %86 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %falseResult_28 {handshake.name = "sink5"} : <i32>
    %trueResult_29, %falseResult_30 = cond_br %96#1, %87 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %falseResult_30 {handshake.name = "sink6"} : <i32>
    %trueResult_31, %falseResult_32 = cond_br %96#2, %result_21 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %97 = merge %falseResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %result_33, %index_34 = control_merge [%falseResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_34 {handshake.name = "sink7"} : <i1>
    %98 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %99 = constant %98 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 4 : i32} : <>, <i32>
    %100 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %101 = constant %100 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %102 = addi %97, %101 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %103:2 = fork [2] %102 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i32>
    %104 = cmpi ne, %103#1, %99 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %105:2 = fork [2] %104 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i1>
    %trueResult_35, %falseResult_36 = cond_br %105#1, %103#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    sink %falseResult_36 {handshake.name = "sink8"} : <i32>
    %trueResult_37, %falseResult_38 = cond_br %105#0, %result_33 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_39, %index_40 = control_merge [%falseResult_38]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_40 {handshake.name = "sink9"} : <i1>
    %106:2 = fork [2] %result_39 {handshake.bb = 6 : ui32, handshake.name = "fork21"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_0, %memEnd, %0#1 : <>, <>, <>
  }
}

