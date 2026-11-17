module {
  handshake.func @test_flatten_array(%arg0: memref<512xi32>, %arg1: memref<512xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["input", "output", "input_start", "output_start", "start"], resNames = ["input_end", "output_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg1 : memref<512xi32>] %arg3 (%58, %addressResult_5, %dataResult_6) %114#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i9>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg0 : memref<512xi32>] %arg2 (%addressResult) %114#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i9>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i2>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%3, %trueResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %6:3 = fork [3] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i2>
    %result, %index = control_merge [%4, %trueResult_37]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %9 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %10 = extui %9 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i3>
    %11 = br %6#2 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i2>
    %12 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i2>
    %13 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i2>
    %14 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %15 = mux %21#3 [%10, %trueResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i3>, <i3>] to <i3>
    %16:3 = fork [3] %15 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i3>
    %17 = extui %16#2 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i3> to <i4>
    %18 = mux %21#2 [%11, %trueResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i2>, <i2>] to <i2>
    %19 = mux %21#0 [%12, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i2>, <i2>] to <i2>
    %20 = mux %21#1 [%13, %trueResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i2>, <i2>] to <i2>
    %result_1, %index_2 = control_merge [%14, %trueResult_31]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %21:4 = fork [4] %index_2 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i1>
    %22:2 = fork [2] %result_1 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 7 : i4} : <>, <i4>
    %25 = subi %24, %17 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i4>
    %26 = constant %22#0 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = false} : <>, <i1>
    %27 = br %26 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i1>
    %28 = extui %27 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i1> to <i4>
    %29 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i2>
    %30 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i2>
    %31 = br %20 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i2>
    %32 = br %16#1 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <i3>
    %33 = br %25 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <i4>
    %34 = br %16#0 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <i3>
    %35 = br %22#1 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <>
    %36 = mux %56#6 [%28, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i4>, <i4>] to <i4>
    %37:3 = fork [3] %36 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i4>
    %38 = extui %37#0 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i4> to <i9>
    %39 = extui %37#1 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i4> to <i5>
    %40 = constant %60 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 1 : i5} : <>, <i5>
    %41 = extui %37#2 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i4> to <i5>
    %42 = mux %56#2 [%29, %trueResult_7] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i2>, <i2>] to <i2>
    %43 = mux %56#0 [%30, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i2>, <i2>] to <i2>
    %44:2 = fork [2] %43 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i2>
    %45 = extui %44#1 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i2> to <i64>
    %46 = mux %56#1 [%31, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i2>, <i2>] to <i2>
    %47:2 = fork [2] %46 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i2>
    %48 = extui %47#1 {handshake.bb = 3 : ui32, handshake.name = "extui12"} : <i2> to <i64>
    %49 = mux %56#4 [%32, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i3>, <i3>] to <i3>
    %50 = mux %56#5 [%33, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i4>, <i4>] to <i4>
    %51:2 = fork [2] %50 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i4>
    %52 = extsi %51#1 {handshake.bb = 3 : ui32, handshake.name = "extsi2"} : <i4> to <i64>
    %53 = mux %56#3 [%34, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i3>, <i3>] to <i3>
    %54:2 = fork [2] %53 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i3>
    %55 = extui %54#1 {handshake.bb = 3 : ui32, handshake.name = "extui13"} : <i3> to <i64>
    %result_3, %index_4 = control_merge [%35, %trueResult_19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %56:7 = fork [7] %index_4 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %57:2 = fork [2] %result_3 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    %58 = constant %57#0 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %59 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %60 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %61 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %62 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %63 = constant %62 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 7 : i64} : <>, <i64>
    %64:2 = fork [2] %63 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i64>
    %65 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %66 = constant %65 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 4 : i64} : <>, <i64>
    %67:2 = fork [2] %66 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i64>
    %68 = constant %61 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 15 : i5} : <>, <i5>
    %69 = subi %68, %41 {handshake.bb = 3 : ui32, handshake.name = "subi1"} : <i5>
    %70 = extsi %69 {handshake.bb = 3 : ui32, handshake.name = "extsi3"} : <i5> to <i9>
    %71 = shli %45, %64#1 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %72 = trunci %71 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i64> to <i9>
    %73 = shli %52, %67#1 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %74 = trunci %73 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i64> to <i9>
    %75 = addi %74, %70 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i9>
    %76 = addi %72, %75 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i9>
    %addressResult, %dataResult = load[%76] %outputs {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i9>, <i32>, <i9>, <i32>
    %77 = shli %48, %64#0 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %78 = trunci %77 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i64> to <i9>
    %79 = shli %55, %67#0 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %80 = trunci %79 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i64> to <i9>
    %81 = addi %80, %38 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i9>
    %82 = addi %78, %81 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i9>
    %addressResult_5, %dataResult_6 = store[%82] %dataResult {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i9>, <i32>, <i9>, <i32>
    %83 = addi %39, %40 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i5>
    %84:2 = fork [2] %83 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i5>
    %85 = trunci %84#0 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i5> to <i4>
    %86 = constant %59 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = -16 : i5} : <>, <i5>
    %87 = cmpi ult, %84#1, %86 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i5>
    %88:8 = fork [8] %87 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult, %falseResult = cond_br %88#0, %85 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i4>
    sink %falseResult {handshake.name = "sink0"} : <i4>
    %trueResult_7, %falseResult_8 = cond_br %88#3, %42 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i2>
    %trueResult_9, %falseResult_10 = cond_br %88#1, %44#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i2>
    %trueResult_11, %falseResult_12 = cond_br %88#2, %47#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i2>
    %trueResult_13, %falseResult_14 = cond_br %88#5, %49 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i3>
    %trueResult_15, %falseResult_16 = cond_br %88#6, %51#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i4>
    sink %falseResult_16 {handshake.name = "sink1"} : <i4>
    %trueResult_17, %falseResult_18 = cond_br %88#4, %54#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i3>
    sink %falseResult_18 {handshake.name = "sink2"} : <i3>
    %trueResult_19, %falseResult_20 = cond_br %88#7, %57#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %89 = merge %falseResult_8 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i2>
    %90 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i2>
    %91 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i2>
    %92 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i3>
    %93 = extui %92 {handshake.bb = 4 : ui32, handshake.name = "extui14"} : <i3> to <i4>
    %94 = constant %96 {handshake.bb = 4 : ui32, handshake.name = "constant22", value = 1 : i4} : <>, <i4>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink3"} : <i1>
    %95 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %96 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %97 = addi %93, %94 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i4>
    %98:2 = fork [2] %97 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i4>
    %99 = trunci %98#0 {handshake.bb = 4 : ui32, handshake.name = "trunci5"} : <i4> to <i3>
    %100 = constant %95 {handshake.bb = 4 : ui32, handshake.name = "constant23", value = -8 : i4} : <>, <i4>
    %101 = cmpi ult, %98#1, %100 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i4>
    %102:5 = fork [5] %101 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_23, %falseResult_24 = cond_br %102#0, %99 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i3>
    sink %falseResult_24 {handshake.name = "sink4"} : <i3>
    %trueResult_25, %falseResult_26 = cond_br %102#3, %89 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i2>
    %trueResult_27, %falseResult_28 = cond_br %102#1, %90 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i2>
    sink %falseResult_28 {handshake.name = "sink5"} : <i2>
    %trueResult_29, %falseResult_30 = cond_br %102#2, %91 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i2>
    sink %falseResult_30 {handshake.name = "sink6"} : <i2>
    %trueResult_31, %falseResult_32 = cond_br %102#4, %result_21 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %103 = merge %falseResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i2>
    %104 = extui %103 {handshake.bb = 5 : ui32, handshake.name = "extui15"} : <i2> to <i3>
    %105 = constant %107 {handshake.bb = 5 : ui32, handshake.name = "constant24", value = 1 : i3} : <>, <i3>
    %result_33, %index_34 = control_merge [%falseResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_34 {handshake.name = "sink7"} : <i1>
    %106 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %107 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %108 = addi %104, %105 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i3>
    %109:2 = fork [2] %108 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i3>
    %110 = trunci %109#0 {handshake.bb = 5 : ui32, handshake.name = "trunci6"} : <i3> to <i2>
    %111 = constant %106 {handshake.bb = 5 : ui32, handshake.name = "constant25", value = -4 : i3} : <>, <i3>
    %112 = cmpi ult, %109#1, %111 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i3>
    %113:2 = fork [2] %112 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i1>
    %trueResult_35, %falseResult_36 = cond_br %113#0, %110 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i2>
    sink %falseResult_36 {handshake.name = "sink8"} : <i2>
    %trueResult_37, %falseResult_38 = cond_br %113#1, %result_33 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_39, %index_40 = control_merge [%falseResult_38]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_40 {handshake.name = "sink9"} : <i1>
    %114:2 = fork [2] %result_39 {handshake.bb = 6 : ui32, handshake.name = "fork21"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_0, %memEnd, %0#1 : <>, <>, <>
  }
}

