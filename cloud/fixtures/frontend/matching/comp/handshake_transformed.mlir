module {
  handshake.func @matching(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["edges", "vertices", "num_edges", "edges_start", "vertices_start", "start"], resNames = ["out0", "edges_end", "vertices_end", "end"]} {
    %0:5 = fork [5] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:3 = lsq[%arg1 : memref<1000xi32>] (%arg4, %14#0, %addressResult_6, %31#0, %addressResult_24, %51#0, %addressResult_40, %dataResult_41, %addressResult_42, %dataResult_43, %71#1)  {groupSizes = [1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult, %addressResult_22) %71#0 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %3 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0.000000e+00 : f32} : <>, <f32>
    %5 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %6:4 = fork [4] %5 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %6#3, %4 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %7 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %6#0, %7 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %falseResult_1 {handshake.name = "sink0"} : <i1>
    %8 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %6#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %6#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %9 = mux %13#0 [%trueResult, %trueResult_46] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %10 = mux %13#1 [%8, %trueResult_48] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %12 = mux %13#2 [%trueResult_2, %trueResult_50] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_52]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %14:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %19 = shli %11#1, %16 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %21 = trunci %20#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %addressResult, %dataResult = load[%21] %outputs#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %22:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %23 = trunci %22#0 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %addressResult_6, %dataResult_7 = load[%23] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %24 = cmpi slt, %dataResult_7, %18 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %25:6 = fork [6] %24 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %25#5, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %25#4, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %25#3, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %25#2, %20#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_15 {handshake.name = "sink2"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %25#1, %22#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink3"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %25#0, %14#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %26 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %27 = merge %trueResult_10 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <f32>
    %28 = merge %trueResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %29 = merge %trueResult_14 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %30 = merge %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <i32>
    %result_20, %index_21 = control_merge [%trueResult_18]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_21 {handshake.name = "sink4"} : <i1>
    %31:2 = lazy_fork [2] %result_20 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %35 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %36 = ori %29, %33 {handshake.bb = 2 : ui32, handshake.name = "ori0"} : <i32>
    %37 = trunci %36 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %addressResult_22, %dataResult_23 = load[%37] %outputs#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %38:2 = fork [2] %dataResult_23 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %39 = trunci %38#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %addressResult_24, %dataResult_25 = load[%39] %2#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load3"} : <i10>, <i32>, <i10>, <i32>
    %40 = cmpi slt, %dataResult_25, %35 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %41:6 = fork [6] %40 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_26, %falseResult_27 = cond_br %41#5, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %41#4, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <f32>
    %trueResult_30, %falseResult_31 = cond_br %41#3, %28 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %41#2, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    sink %falseResult_33 {handshake.name = "sink5"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %41#1, %38#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    sink %falseResult_35 {handshake.name = "sink6"} : <i32>
    %trueResult_36, %falseResult_37 = cond_br %41#0, %31#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %42 = merge %trueResult_26 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %43 = merge %trueResult_28 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <f32>
    %44 = merge %trueResult_30 {handshake.bb = 3 : ui32, handshake.name = "merge7"} : <i32>
    %45 = merge %trueResult_32 {handshake.bb = 3 : ui32, handshake.name = "merge8"} : <i32>
    %46:2 = fork [2] %45 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %47 = trunci %46#1 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i32> to <i10>
    %48 = merge %trueResult_34 {handshake.bb = 3 : ui32, handshake.name = "merge9"} : <i32>
    %49:2 = fork [2] %48 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %50 = trunci %49#0 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i32> to <i10>
    %result_38, %index_39 = control_merge [%trueResult_36]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_39 {handshake.name = "sink7"} : <i1>
    %51:2 = lazy_fork [2] %result_38 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %53 = constant %52 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1.000000e+00 : f32} : <>, <f32>
    %addressResult_40, %dataResult_41 = store[%47] %49#1 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store4"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_42, %dataResult_43 = store[%50] %46#0 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store5"} : <i10>, <i32>, <i10>, <i32>
    %54 = addf %43, %53 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %55 = br %54 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <f32>
    %56 = br %42 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <i32>
    %57 = br %44 {handshake.bb = 3 : ui32, handshake.name = "br3"} : <i32>
    %58 = br %51#1 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <>
    %59 = mux %63#0 [%falseResult_11, %falseResult_29, %55] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i2>, [<f32>, <f32>, <f32>] to <f32>
    %60 = mux %63#1 [%falseResult_9, %falseResult_27, %56] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %61:2 = fork [2] %60 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i32>
    %62 = mux %63#2 [%falseResult_13, %falseResult_31, %57] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_44, %index_45 = control_merge [%falseResult_19, %falseResult_37, %58]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>, <>] to <>, <i2>
    %63:3 = fork [3] %index_45 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i2>
    %64 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %65 = constant %64 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %66 = addi %62, %65 {handshake.bb = 4 : ui32, handshake.name = "addi0"} : <i32>
    %67:2 = fork [2] %66 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i32>
    %68 = cmpi slt, %67#1, %61#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %69:4 = fork [4] %68 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %trueResult_46, %falseResult_47 = cond_br %69#3, %59 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <f32>
    %trueResult_48, %falseResult_49 = cond_br %69#2, %67#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    sink %falseResult_49 {handshake.name = "sink8"} : <i32>
    %trueResult_50, %falseResult_51 = cond_br %69#1, %61#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    sink %falseResult_51 {handshake.name = "sink9"} : <i32>
    %trueResult_52, %falseResult_53 = cond_br %69#0, %result_44 {handshake.bb = 4 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %70 = mux %index_55 [%falseResult, %falseResult_47] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %result_54, %index_55 = control_merge [%falseResult_5, %falseResult_53]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %71:2 = fork [2] %result_54 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %70, %memEnd, %2#2, %0#1 : <f32>, <>, <>, <>
  }
}

