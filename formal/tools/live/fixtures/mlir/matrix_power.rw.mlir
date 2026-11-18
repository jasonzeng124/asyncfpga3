module {
  handshake.func @matrix_power(%arg0: memref<400xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mat", "row", "col", "a", "mat_start", "row_start", "col_start", "a_start", "start"], resNames = ["mat_end", "row_end", "col_end", "a_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg3 : memref<20xi32>] %arg7 (%addressResult) %78#3 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg2 : memref<20xi32>] %arg6 (%addressResult_6) %78#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %outputs_2, %memEnd_3 = mem_controller[%arg1 : memref<20xi32>] %arg5 (%addressResult_10) %78#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %1:3 = lsq[%arg0 : memref<400xi32>] (%arg4, %35#0, %addressResult_8, %addressResult_12, %addressResult_14, %dataResult_15, %78#0)  {groupSizes = [3 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i9>, !handshake.channel<i9>, !handshake.channel<i9>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i5>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%4, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %8 = extui %7#2 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i5> to <i7>
    %9 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -1 : i7} : <>, <i7>
    %result, %index = control_merge [%5, %trueResult_28]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = addi %8, %9 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i7>
    %13 = constant %10#0 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %14 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %15 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i1> to <i5>
    %16 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i5>
    %17 = br %12 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i7>
    %18 = br %7#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i5>
    %19 = br %10#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <>
    %20 = mux %34#3 [%15, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %21:4 = fork [4] %20 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %22 = extui %21#3 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i5> to <i6>
    %23 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i6} : <>, <i6>
    %24 = mux %34#1 [%16, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %25 = mux %34#2 [%17, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i7>, <i7>] to <i7>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i7>
    %27 = extsi %26#1 {handshake.bb = 2 : ui32, handshake.name = "extsi2"} : <i7> to <i32>
    %28 = extui %27 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %29:2 = fork [2] %28 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i64>
    %30 = mux %34#0 [%18, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %31:2 = fork [2] %30 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %32 = extui %31#1 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i5> to <i64>
    %33:2 = fork [2] %32 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %result_4, %index_5 = control_merge [%19, %trueResult_22]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %34:4 = fork [4] %index_5 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %35:2 = fork [2] %result_4 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <>
    %36 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %40:2 = fork [2] %39 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i64>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %42 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i64} : <>, <i64>
    %43:2 = fork [2] %42 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i64>
    %addressResult, %dataResult = load[%21#2] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %addressResult_6, %dataResult_7 = load[%21#1] %outputs_0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i5>, <i32>, <i5>, <i32>
    %44 = trunci %dataResult_7 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i9>
    %45 = shli %29#0, %43#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %46 = trunci %45 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i9>
    %47 = shli %29#1, %40#1 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %48 = trunci %47 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i9>
    %49 = addi %46, %48 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i9>
    %50 = addi %49, %44 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i9>
    %addressResult_8, %dataResult_9 = load[%50] %1#0 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : false}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i9>, <i32>, <i9>, <i32>
    %51 = muli %dataResult, %dataResult_9 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %addressResult_10, %dataResult_11 = load[%21#0] %outputs_2 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i5>, <i32>, <i5>, <i32>
    %52 = trunci %dataResult_11 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i9>
    %53 = shli %33#0, %43#0 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %54 = trunci %53 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i64> to <i9>
    %55 = shli %33#1, %40#0 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %56 = trunci %55 {handshake.bb = 2 : ui32, handshake.name = "trunci5"} : <i64> to <i9>
    %57 = addi %54, %56 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i9>
    %58 = addi %57, %52 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i9>
    %59:2 = fork [2] %58 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i9>
    %addressResult_12, %dataResult_13 = load[%59#1] %1#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : false}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load4"} : <i9>, <i32>, <i9>, <i32>
    %60 = addi %dataResult_13, %51 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_14, %dataResult_15 = store[%59#0] %60 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : <i9>, <i32>, <i9>, <i32>
    %61 = addi %22, %23 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i6>
    %62:2 = fork [2] %61 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i6>
    %63 = trunci %62#0 {handshake.bb = 2 : ui32, handshake.name = "trunci6"} : <i6> to <i5>
    %64 = constant %36 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 20 : i6} : <>, <i6>
    %65 = cmpi ult, %62#1, %64 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i6>
    %66:5 = fork [5] %65 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult, %falseResult = cond_br %66#0, %63 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink0"} : <i5>
    %trueResult_16, %falseResult_17 = cond_br %66#2, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i5>
    %trueResult_18, %falseResult_19 = cond_br %66#3, %26#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i7>
    sink %falseResult_19 {handshake.name = "sink1"} : <i7>
    %trueResult_20, %falseResult_21 = cond_br %66#1, %31#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    sink %falseResult_21 {handshake.name = "sink2"} : <i5>
    %trueResult_22, %falseResult_23 = cond_br %66#4, %35#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %67 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i5>
    %68 = extui %67 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i5> to <i6>
    %69 = constant %71 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i6} : <>, <i6>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_25 {handshake.name = "sink3"} : <i1>
    %70 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %71 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %72 = addi %68, %69 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i6>
    %73:2 = fork [2] %72 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i6>
    %74 = trunci %73#0 {handshake.bb = 3 : ui32, handshake.name = "trunci7"} : <i6> to <i5>
    %75 = constant %70 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 20 : i6} : <>, <i6>
    %76 = cmpi ult, %73#1, %75 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i6>
    %77:2 = fork [2] %76 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult_26, %falseResult_27 = cond_br %77#0, %74 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    sink %falseResult_27 {handshake.name = "sink4"} : <i5>
    %trueResult_28, %falseResult_29 = cond_br %77#1, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_30, %index_31 = control_merge [%falseResult_29]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_31 {handshake.name = "sink5"} : <i1>
    %78:4 = fork [4] %result_30 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %1#2, %memEnd_3, %memEnd_1, %memEnd, %0#1 : <>, <>, <>, <>, <>
  }
}

