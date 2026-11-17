module {
  handshake.func @matching_2(%arg0: memref<1000xi32>, %arg1: memref<1000xf32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["edges", "vertices", "num_edges", "edges_start", "vertices_start", "start"], resNames = ["edges_end", "vertices_end", "end"]} {
    %0:4 = fork [4] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:3 = lsq[%arg1 : memref<1000xf32>] (%arg4, %12#0, %addressResult_4, %28#0, %addressResult_20, %47#0, %addressResult_34, %dataResult_35, %addressResult_36, %dataResult_37, %63#1)  {groupSizes = [1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<f32>, !handshake.channel<i10>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult, %addressResult_18) %63#0 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %8 = mux %11#0 [%7, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = mux %11#1 [%trueResult_0, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %12:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0.000000e+00 : f32} : <>, <f32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %17 = shli %9#1, %16 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %18:2 = fork [2] %17 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %19 = trunci %18#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %addressResult, %dataResult = load[%19] %outputs#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %20:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %21 = trunci %20#0 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %addressResult_4, %dataResult_5 = load[%21] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %22 = cmpf olt, %dataResult_5, %14 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %23:5 = fork [5] %22 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %23#4, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %23#3, %9#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %23#2, %18#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %23#1, %20#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink3"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %23#0, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %24 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %25 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %26 = merge %trueResult_10 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %27 = merge %trueResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_16, %index_17 = control_merge [%trueResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink4"} : <i1>
    %28:2 = lazy_fork [2] %result_16 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 0.000000e+00 : f32} : <>, <f32>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %33 = ori %26, %32 {handshake.bb = 2 : ui32, handshake.name = "ori0"} : <i32>
    %34 = trunci %33 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %addressResult_18, %dataResult_19 = load[%34] %outputs#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %35:2 = fork [2] %dataResult_19 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %36 = trunci %35#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %addressResult_20, %dataResult_21 = load[%36] %2#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load3"} : <i10>, <f32>, <i10>, <f32>
    %37 = cmpf olt, %dataResult_21, %30 {handshake.bb = 2 : ui32, handshake.name = "cmpf1"} : <f32>
    %38:5 = fork [5] %37 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_22, %falseResult_23 = cond_br %38#4, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %38#3, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %38#2, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %falseResult_27 {handshake.name = "sink5"} : <i32>
    %trueResult_28, %falseResult_29 = cond_br %38#1, %35#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    sink %falseResult_29 {handshake.name = "sink6"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %38#0, %28#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %39 = merge %trueResult_22 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %40 = merge %trueResult_24 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %41 = merge %trueResult_26 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <i32>
    %42:2 = fork [2] %41 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %43 = trunci %42#0 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i32> to <i10>
    %44 = merge %trueResult_28 {handshake.bb = 3 : ui32, handshake.name = "merge7"} : <i32>
    %45:2 = fork [2] %44 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %46 = trunci %45#0 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i32> to <i10>
    %result_32, %index_33 = control_merge [%trueResult_30]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_33 {handshake.name = "sink7"} : <i1>
    %47:2 = lazy_fork [2] %result_32 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %48 = sitofp %45#1 {handshake.bb = 3 : ui32, handshake.name = "sitofp0"} : <i32> to <f32>
    %addressResult_34, %dataResult_35 = store[%43] %48 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store4"} : <i10>, <f32>, <i10>, <f32>
    %49 = sitofp %42#1 {handshake.bb = 3 : ui32, handshake.name = "sitofp1"} : <i32> to <f32>
    %addressResult_36, %dataResult_37 = store[%46] %49 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store5"} : <i10>, <f32>, <i10>, <f32>
    %50 = br %39 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <i32>
    %51 = br %40 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <i32>
    %52 = br %47#1 {handshake.bb = 3 : ui32, handshake.name = "br3"} : <>
    %53 = mux %56#0 [%falseResult_7, %falseResult_23, %50] {handshake.bb = 4 : ui32, handshake.name = "mux2"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %54:2 = fork [2] %53 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i32>
    %55 = mux %56#1 [%falseResult_9, %falseResult_25, %51] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_38, %index_39 = control_merge [%falseResult_15, %falseResult_31, %52]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>, <>] to <>, <i2>
    %56:2 = fork [2] %index_39 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i2>
    %57 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %58 = constant %57 {handshake.bb = 4 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %59 = addi %55, %58 {handshake.bb = 4 : ui32, handshake.name = "addi0"} : <i32>
    %60:2 = fork [2] %59 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i32>
    %61 = cmpi slt, %60#1, %54#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %62:3 = fork [3] %61 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %trueResult_40, %falseResult_41 = cond_br %62#2, %60#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    sink %falseResult_41 {handshake.name = "sink8"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %62#1, %54#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    sink %falseResult_43 {handshake.name = "sink9"} : <i32>
    %trueResult_44, %falseResult_45 = cond_br %62#0, %result_38 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_3, %falseResult_45]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    sink %index_47 {handshake.name = "sink10"} : <i1>
    %63:2 = fork [2] %result_46 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %memEnd, %2#2, %0#1 : <>, <>, <>
  }
}

