module {
  handshake.func @matvec(%arg0: memref<10000xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["m", "v", "out", "m_start", "v_start", "out_start", "start"], resNames = ["out0", "m_end", "v_end", "out_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<100xi32>] %arg5 (%60, %addressResult_17, %dataResult_18) %70#2 {connectedBlocks = [3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<100xi32>] %arg4 (%addressResult) %70#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<10000xi32>] %arg3 (%addressResult_5) %70#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i14>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i7>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%3, %trueResult_19] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %6:2 = fork [2] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %result, %index = control_merge [%4, %trueResult_21]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %9 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %11 = extui %10#1 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %12 = extui %10#0 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i1> to <i7>
    %13 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i7>
    %14 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i7>
    %15 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %16 = mux %27#2 [%12, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i7>, <i7>] to <i7>
    %17:3 = fork [3] %16 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i7>
    %18 = extui %17#0 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i7> to <i14>
    %19 = extui %17#2 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i7> to <i8>
    %20 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i8} : <>, <i8>
    %21 = mux %27#3 [%11, %trueResult_7] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %22 = mux %27#1 [%13, %trueResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i7>, <i7>] to <i7>
    %23 = mux %27#0 [%14, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i7>, <i7>] to <i7>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i7>
    %25 = extui %24#1 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i7> to <i64>
    %26:3 = fork [3] %25 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i64>
    %result_3, %index_4 = control_merge [%15, %trueResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %27:4 = fork [4] %index_4 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 6 : i64} : <>, <i64>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 5 : i64} : <>, <i64>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %35 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i64} : <>, <i64>
    %addressResult, %dataResult = load[%17#1] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %36 = shli %26#0, %35 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %37 = trunci %36 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i14>
    %38 = shli %26#1, %33 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %39 = trunci %38 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i14>
    %40 = shli %26#2, %31 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %41 = trunci %40 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i14>
    %42 = addi %39, %41 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i14>
    %43 = addi %37, %42 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i14>
    %44 = addi %43, %18 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i14>
    %addressResult_5, %dataResult_6 = load[%44] %outputs_1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i14>, <i32>, <i14>, <i32>
    %45 = muli %dataResult, %dataResult_6 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %46 = addi %21, %45 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %47 = addi %19, %20 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i8>
    %48:2 = fork [2] %47 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i8>
    %49 = trunci %48#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i8> to <i7>
    %50 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 100 : i8} : <>, <i8>
    %51 = cmpi ult, %48#1, %50 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i8>
    %52:5 = fork [5] %51 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult, %falseResult = cond_br %52#0, %49 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i7>
    sink %falseResult {handshake.name = "sink0"} : <i7>
    %trueResult_7, %falseResult_8 = cond_br %52#3, %46 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %52#2, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i7>
    %trueResult_11, %falseResult_12 = cond_br %52#1, %24#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i7>
    sink %falseResult_12 {handshake.name = "sink1"} : <i7>
    %trueResult_13, %falseResult_14 = cond_br %52#4, %result_3 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %53 = merge %falseResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %54:2 = fork [2] %53 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %55 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i7>
    %56:2 = fork [2] %55 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i7>
    %57 = extui %56#1 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i7> to <i8>
    %58 = constant %62 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 1 : i8} : <>, <i8>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_16 {handshake.name = "sink2"} : <i1>
    %59:2 = fork [2] %result_15 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    %60 = constant %59#0 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %61 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %62 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %addressResult_17, %dataResult_18 = store[%56#0] %54#0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i7>, <i32>, <i7>, <i32>
    %63 = addi %57, %58 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i8>
    %64:2 = fork [2] %63 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i8>
    %65 = trunci %64#0 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i8> to <i7>
    %66 = constant %61 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 100 : i8} : <>, <i8>
    %67 = cmpi ult, %64#1, %66 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i8>
    %68:3 = fork [3] %67 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_19, %falseResult_20 = cond_br %68#0, %65 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i7>
    sink %falseResult_20 {handshake.name = "sink3"} : <i7>
    %trueResult_21, %falseResult_22 = cond_br %68#1, %59#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %trueResult_23, %falseResult_24 = cond_br %68#2, %54#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %trueResult_23 {handshake.name = "sink4"} : <i32>
    %69 = merge %falseResult_24 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_25, %index_26 = control_merge [%falseResult_22]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_26 {handshake.name = "sink5"} : <i1>
    %70:3 = fork [3] %result_25 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %69, %memEnd_2, %memEnd_0, %memEnd, %0#1 : <i32>, <>, <>, <>, <>
  }
}

