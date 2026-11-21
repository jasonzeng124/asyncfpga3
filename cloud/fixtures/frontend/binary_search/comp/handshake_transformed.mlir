module {
  handshake.func @binary_search(%arg0: !handshake.channel<i32>, %arg1: memref<101xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["search", "a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:3 = fork [3] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<101xi32>] %arg2 (%addressResult, %addressResult_18) %result_40 {connectedBlocks = [1 : i32, 4 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i7>, !handshake.channel<i7>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i7>
    %4 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %6 = mux %10#0 [%3, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %7:2 = fork [2] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %8 = mux %10#1 [%4, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %result, %index = control_merge [%5, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %addressResult, %dataResult = load[%7#0] %outputs#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %11 = cmpi eq, %dataResult, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %12:3 = fork [3] %11 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %12#0, %7#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i7>
    %13 = extui %trueResult {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i7> to <i8>
    %trueResult_0, %falseResult_1 = cond_br %12#2, %9#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %12#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %14 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %15 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i7>
    %16 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i7> to <i8>
    %17 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 2 : i8} : <>, <i8>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink0"} : <i1>
    %18:2 = fork [2] %result_4 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %21 = addi %16, %17 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i8>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i8>
    %23 = trunci %22#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %24 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 101 : i8} : <>, <i8>
    %25 = cmpi ult, %22#1, %24 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i8>
    %26:4 = fork [4] %25 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %26#0, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i7>
    sink %falseResult_7 {handshake.name = "sink1"} : <i7>
    %trueResult_8, %falseResult_9 = cond_br %26#1, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %26#2, %18#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %27 = constant %18#0 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = true} : <>, <i1>
    %trueResult_12, %falseResult_13 = cond_br %26#3, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i1>
    sink %trueResult_12 {handshake.name = "sink2"} : <i1>
    %28 = extsi %falseResult_13 {handshake.bb = 2 : ui32, handshake.name = "extsi0"} : <i1> to <i8>
    %29 = mux %31#0 [%13, %28] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i8>, <i8>] to <i8>
    %30 = mux %31#1 [%trueResult_0, %falseResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_2, %falseResult_11]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %31:2 = fork [2] %index_15 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %32:2 = fork [2] %result_14 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <>
    %33 = constant %32#0 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = true} : <>, <i1>
    %34 = br %33 {handshake.bb = 3 : ui32, handshake.name = "br5"} : <i1>
    %35 = extui %34 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i1> to <i7>
    %36 = br %30 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i32>
    %37 = br %29 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <i8>
    %38 = br %32#1 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <>
    %39 = mux %44#1 [%35, %trueResult_30] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i7>, <i7>] to <i7>
    %40:2 = fork [2] %39 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <i7>
    %41 = mux %44#2 [%36, %trueResult_32] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %42:2 = fork [2] %41 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <i32>
    %43 = mux %44#0 [%37, %trueResult_34] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i8>, <i8>] to <i8>
    %result_16, %index_17 = control_merge [%38, %trueResult_36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %44:3 = fork [3] %index_17 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i1>
    %addressResult_18, %dataResult_19 = load[%40#0] %outputs#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i7>, <i32>, <i7>, <i32>
    %45 = cmpi eq, %dataResult_19, %42#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %46:4 = fork [4] %45 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_20, %falseResult_21 = cond_br %46#1, %40#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i7>
    %47 = extui %trueResult_20 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i7> to <i8>
    %trueResult_22, %falseResult_23 = cond_br %46#0, %43 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i8>
    %trueResult_24, %falseResult_25 = cond_br %46#3, %result_16 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_26, %falseResult_27 = cond_br %46#2, %42#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %trueResult_26 {handshake.name = "sink3"} : <i32>
    %48 = merge %falseResult_27 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %49 = merge %falseResult_23 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i8>
    %50 = merge %falseResult_21 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i7>
    %51 = extui %50 {handshake.bb = 5 : ui32, handshake.name = "extui7"} : <i7> to <i8>
    %52 = constant %55 {handshake.bb = 5 : ui32, handshake.name = "constant14", value = 2 : i8} : <>, <i8>
    %result_28, %index_29 = control_merge [%falseResult_25]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_29 {handshake.name = "sink4"} : <i1>
    %53:2 = fork [2] %result_28 {handshake.bb = 5 : ui32, handshake.name = "fork14"} : <>
    %54 = source {handshake.bb = 5 : ui32, handshake.name = "source2"} : <>
    %55 = source {handshake.bb = 5 : ui32, handshake.name = "source3"} : <>
    %56 = addi %51, %52 {handshake.bb = 5 : ui32, handshake.name = "addi1"} : <i8>
    %57:2 = fork [2] %56 {handshake.bb = 5 : ui32, handshake.name = "fork15"} : <i8>
    %58 = trunci %57#0 {handshake.bb = 5 : ui32, handshake.name = "trunci1"} : <i8> to <i7>
    %59 = constant %54 {handshake.bb = 5 : ui32, handshake.name = "constant15", value = 101 : i8} : <>, <i8>
    %60 = cmpi ult, %57#1, %59 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i8>
    %61:5 = fork [5] %60 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult_30, %falseResult_31 = cond_br %61#0, %58 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i7>
    sink %falseResult_31 {handshake.name = "sink5"} : <i7>
    %trueResult_32, %falseResult_33 = cond_br %61#2, %48 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    sink %falseResult_33 {handshake.name = "sink6"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %61#1, %49 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <i8>
    %trueResult_36, %falseResult_37 = cond_br %61#3, %53#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %62 = constant %53#0 {handshake.bb = 5 : ui32, handshake.name = "constant16", value = true} : <>, <i1>
    %trueResult_38, %falseResult_39 = cond_br %61#4, %62 {handshake.bb = 5 : ui32, handshake.name = "cond_br19"} : <i1>, <i1>
    sink %trueResult_38 {handshake.name = "sink7"} : <i1>
    %63 = extsi %falseResult_39 {handshake.bb = 5 : ui32, handshake.name = "extsi1"} : <i1> to <i8>
    %64 = mux %67#1 [%47, %63] {handshake.bb = 6 : ui32, handshake.name = "mux7"} : <i1>, [<i8>, <i8>] to <i8>
    %65 = mux %67#0 [%trueResult_22, %falseResult_35] {handshake.bb = 6 : ui32, handshake.name = "mux8"} : <i1>, [<i8>, <i8>] to <i8>
    %66:2 = fork [2] %65 {handshake.bb = 6 : ui32, handshake.name = "fork17"} : <i8>
    %result_40, %index_41 = control_merge [%trueResult_24, %falseResult_37]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %67:2 = fork [2] %index_41 {handshake.bb = 6 : ui32, handshake.name = "fork18"} : <i1>
    %68 = source {handshake.bb = 6 : ui32, handshake.name = "source4"} : <>
    %69 = constant %68 {handshake.bb = 6 : ui32, handshake.name = "constant17", value = -1 : i8} : <>, <i8>
    %70 = cmpi eq, %66#1, %69 {handshake.bb = 6 : ui32, handshake.name = "cmpi4"} : <i8>
    %71 = select %70[%64, %66#0] {handshake.bb = 6 : ui32, handshake.name = "select1"} : <i1>, <i8>
    %72 = extsi %71 {handshake.bb = 6 : ui32, handshake.name = "extsi2"} : <i8> to <i32>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %72, %memEnd, %0#1 : <i32>, <>, <>
  }
}

