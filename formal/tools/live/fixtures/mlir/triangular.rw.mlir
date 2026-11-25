module {
  handshake.func @triangular(%arg0: memref<10xi32>, %arg1: !handshake.channel<i32>, %arg2: memref<100xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "n", "a", "x_start", "a_start", "start"], resNames = ["x_end", "a_end", "end"]} {
    %0:2 = fork [2] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %outputs:2, %memEnd = mem_controller[%arg2 : memref<100xi32>] %arg4 (%45, %addressResult, %2#1, %2#2, %2#3) %78#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %2:4 = lsq[MC] (%44#0, %addressResult_28, %addressResult_30, %dataResult_31, %outputs#1)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>)
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<10xi32>] %arg3 (%addressResult_26) %78#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %3 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %4 = constant %3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %5 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %7 = addi %1#2, %4 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %8 = cmpi sgt, %1#1, %6 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %9:3 = fork [3] %8 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %9#2, %7 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %9#1, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %10:2 = fork [2] %trueResult_2 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %9#0, %0#1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %11 = mux %14#0 [%falseResult_19, %falseResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %14#1 [%falseResult_21, %falseResult_37] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %13:3 = fork [3] %12 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%falseResult_23, %falseResult_39]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = -1 : i32} : <>, <i32>
    %19 = addi %13#2, %18 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %20 = cmpi sgt, %13#1, %16 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %21:4 = fork [4] %20 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %21#3, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %21#2, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %21#1, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink4"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %21#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %22 = mux %25#0 [%trueResult, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %23 = mux %25#1 [%10#1, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %24 = mux %25#2 [%10#0, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %25:3 = fork [3] %index_15 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = -2 : i32} : <>, <i32>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %29 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = -1 : i32} : <>, <i32>
    %30 = addi %23, %27 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %31:2 = fork [2] %30 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %32 = cmpi sgt, %31#1, %29 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %33:4 = fork [4] %32 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %33#3, %31#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink5"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %33#2, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %33#1, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %33#0, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %34 = mux %43#0 [%trueResult_16, %trueResult_32] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %35:3 = fork [3] %34 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %36 = mux %43#1 [%trueResult_18, %trueResult_34] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %37:2 = fork [2] %36 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %38 = trunci %37#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %39 = mux %43#2 [%trueResult_20, %trueResult_36] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %40:3 = fork [3] %39 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %41 = trunci %40#0 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i32> to <i7>
    %42 = trunci %40#1 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i32> to <i4>
    %result_24, %index_25 = control_merge [%trueResult_22, %trueResult_38]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %43:3 = fork [3] %index_25 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %44:3 = fork [3] %result_24 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <>
    %45 = constant %44#1 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %47 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = -1 : i32} : <>, <i32>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i32>
    %49 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %50 = constant %49 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 3 : i64} : <>, <i64>
    %51:2 = fork [2] %50 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i64>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %53 = constant %52 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 1 : i64} : <>, <i64>
    %54:2 = fork [2] %53 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i64>
    %55 = extsi %35#2 {handshake.bb = 3 : ui32, handshake.name = "extsi0"} : <i32> to <i64>
    %56:2 = fork [2] %55 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <i64>
    %57 = shli %56#1, %54#1 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %58 = trunci %57 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i64> to <i7>
    %59 = shli %56#0, %51#1 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %60 = trunci %59 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i64> to <i7>
    %61 = addi %58, %60 {handshake.bb = 3 : ui32, handshake.name = "addi6"} : <i7>
    %62 = addi %61, %41 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i7>
    %addressResult, %dataResult = load[%62] %outputs#0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %addressResult_26, %dataResult_27 = load[%42] %outputs_0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i4>, <i32>, <i4>, <i32>
    %63 = muli %dataResult, %dataResult_27 {handshake.bb = 3 : ui32, handshake.name = "muli1"} : <i32>
    %64 = extsi %35#1 {handshake.bb = 3 : ui32, handshake.name = "extsi3"} : <i32> to <i64>
    %65:2 = fork [2] %64 {handshake.bb = 3 : ui32, handshake.name = "fork19"} : <i64>
    %66 = shli %65#1, %54#0 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %67 = trunci %66 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i64> to <i7>
    %68 = shli %65#0, %51#0 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %69 = trunci %68 {handshake.bb = 3 : ui32, handshake.name = "trunci6"} : <i64> to <i7>
    %70 = addi %67, %69 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i7>
    %71 = addi %70, %38 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i7>
    %72:2 = fork [2] %71 {handshake.bb = 3 : ui32, handshake.name = "fork20"} : <i7>
    %addressResult_28, %dataResult_29 = load[%72#1] %2#0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i7>, <i32>, <i7>, <i32>
    %73 = subi %dataResult_29, %63 {handshake.bb = 3 : ui32, handshake.name = "subi0"} : <i32>
    %addressResult_30, %dataResult_31 = store[%72#0] %73 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : <i7>, <i32>, <i7>, <i32>
    %74 = addi %35#0, %48#1 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %75:2 = fork [2] %74 {handshake.bb = 3 : ui32, handshake.name = "fork21"} : <i32>
    %76 = cmpi sgt, %75#1, %48#0 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %77:4 = fork [4] %76 {handshake.bb = 3 : ui32, handshake.name = "fork22"} : <i1>
    %trueResult_32, %falseResult_33 = cond_br %77#3, %75#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    sink %falseResult_33 {handshake.name = "sink6"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %77#2, %37#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %77#1, %40#2 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_38, %falseResult_39 = cond_br %77#0, %44#2 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %result_40, %index_41 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %index_41 {handshake.name = "sink7"} : <i1>
    %78:2 = fork [2] %result_40 {handshake.bb = 4 : ui32, handshake.name = "fork23"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %0#0 : <>, <>, <>
  }
}

