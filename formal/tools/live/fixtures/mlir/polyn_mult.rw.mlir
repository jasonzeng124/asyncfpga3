module {
  handshake.func @polyn_mult(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "out", "a_start", "b_start", "out_start", "start"], resNames = ["out0", "a_end", "b_end", "out_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:3 = lsq[%arg2 : memref<100xi32>] (%arg5, %9#0, %addressResult, %dataResult, %31#0, %addressResult_14, %addressResult_16, %dataResult_17, %69#0, %addressResult_34, %addressResult_36, %dataResult_37, %97#2)  {groupSizes = [1 : i32, 2 : i32, 2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg4 (%addressResult_12, %addressResult_32) %97#1 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i7>, !handshake.channel<i7>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<100xi32>] %arg3 (%addressResult_10, %addressResult_30) %97#0 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i7>, !handshake.channel<i7>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui7"} : <i1> to <i7>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%4, %trueResult_48] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %8 = extui %7#2 {handshake.bb = 1 : ui32, handshake.name = "extui8"} : <i7> to <i8>
    %result, %index = control_merge [%5, %trueResult_50]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %10:3 = fork [3] %9#2 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = constant %10#2 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%7#0] %12 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store0"} : <i7>, <i32>, <i7>, <i32>
    %13 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 100 : i8} : <>, <i8>
    %14 = subi %13, %8 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i8>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i8>
    %16 = constant %10#0 {handshake.bb = 1 : ui32, handshake.name = "constant13", value = 1 : i8} : <>, <i8>
    %17 = cmpi ugt, %15#1, %16 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i8>
    %18:4 = fork [4] %17 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %19 = constant %10#1 {handshake.bb = 1 : ui32, handshake.name = "constant14", value = true} : <>, <i1>
    %trueResult, %falseResult = cond_br %18#3, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %20 = extui %trueResult {handshake.bb = 1 : ui32, handshake.name = "extui9"} : <i1> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %18#0, %7#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i7>
    %trueResult_4, %falseResult_5 = cond_br %18#1, %15#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i8>
    sink %falseResult_5 {handshake.name = "sink1"} : <i8>
    %trueResult_6, %falseResult_7 = cond_br %18#2, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %21 = mux %30#2 [%20, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %22:3 = fork [3] %21 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %23 = trunci %22#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %24 = trunci %22#1 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i7>
    %25 = mux %30#0 [%trueResult_2, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i7>, <i7>] to <i7>
    %26:4 = fork [4] %25 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i7>
    %27 = mux %30#1 [%trueResult_4, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i8>, <i8>] to <i8>
    %28:2 = fork [2] %27 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i8>
    %29 = extsi %28#1 {handshake.bb = 2 : ui32, handshake.name = "extsi0"} : <i8> to <i32>
    %result_8, %index_9 = control_merge [%trueResult_6, %trueResult_24]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %30:3 = fork [3] %index_9 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %31:2 = lazy_fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %35 = addi %26#0, %23 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i7>
    %addressResult_10, %dataResult_11 = load[%35] %outputs_0#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i7>, <i32>, <i7>, <i32>
    %36 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = -28 : i7} : <>, <i7>
    %37 = subi %36, %24 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i7>
    %addressResult_12, %dataResult_13 = load[%37] %outputs#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i7>, <i32>, <i7>, <i32>
    %38 = muli %dataResult_11, %dataResult_13 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %addressResult_14, %dataResult_15 = load[%26#2] %1#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load3"} : <i7>, <i32>, <i7>, <i32>
    %39 = addi %dataResult_15, %38 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %addressResult_16, %dataResult_17 = store[%26#1] %39 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store4"} : <i7>, <i32>, <i7>, <i32>
    %40 = addi %22#2, %33 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %41:2 = fork [2] %40 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %42 = cmpi ult, %41#1, %29 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %43:4 = fork [4] %42 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %43#3, %41#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_19 {handshake.name = "sink2"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %43#0, %26#3 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i7>
    %trueResult_22, %falseResult_23 = cond_br %43#1, %28#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i8>
    sink %falseResult_23 {handshake.name = "sink3"} : <i8>
    %trueResult_24, %falseResult_25 = cond_br %43#2, %31#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %44 = mux %index_27 [%falseResult_3, %falseResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i7>, <i7>] to <i7>
    %45:2 = fork [2] %44 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i7>
    %46 = extui %45#1 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i7> to <i8>
    %47 = constant %49 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i8} : <>, <i8>
    %result_26, %index_27 = control_merge [%falseResult_7, %falseResult_25]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %48:2 = fork [2] %result_26 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    %49 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %50 = addi %46, %47 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i8>
    %51 = constant %48#0 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = false} : <>, <i1>
    %52 = br %51 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <i1>
    %53 = extui %52 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i1> to <i8>
    %54 = br %45#0 {handshake.bb = 3 : ui32, handshake.name = "br5"} : <i7>
    %55 = br %50 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i8>
    %56 = br %48#1 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <>
    %57 = mux %68#0 [%53, %78] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i8>, <i8>] to <i8>
    %58:3 = fork [3] %57 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i8>
    %59 = extui %58#2 {handshake.bb = 4 : ui32, handshake.name = "extui12"} : <i8> to <i9>
    %60 = constant %70 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 1 : i9} : <>, <i9>
    %61 = trunci %58#0 {handshake.bb = 4 : ui32, handshake.name = "trunci2"} : <i8> to <i7>
    %62 = trunci %58#1 {handshake.bb = 4 : ui32, handshake.name = "trunci3"} : <i8> to <i7>
    %63 = mux %68#1 [%54, %trueResult_40] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i7>, <i7>] to <i7>
    %64:4 = fork [4] %63 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i7>
    %65 = mux %68#2 [%55, %trueResult_42] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i8>, <i8>] to <i8>
    %66:2 = fork [2] %65 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i8>
    %67 = extui %66#0 {handshake.bb = 4 : ui32, handshake.name = "extui13"} : <i8> to <i9>
    %result_28, %index_29 = control_merge [%56, %trueResult_44]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %68:3 = fork [3] %index_29 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i1>
    %69:2 = lazy_fork [2] %result_28 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork2"} : <>
    %70 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %71 = subi %64#0, %61 {handshake.bb = 4 : ui32, handshake.name = "subi2"} : <i7>
    %addressResult_30, %dataResult_31 = load[%71] %outputs_0#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load5"} : <i7>, <i32>, <i7>, <i32>
    %addressResult_32, %dataResult_33 = load[%62] %outputs#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load6"} : <i7>, <i32>, <i7>, <i32>
    %72 = muli %dataResult_31, %dataResult_33 {handshake.bb = 4 : ui32, handshake.name = "muli1"} : <i32>
    %addressResult_34, %dataResult_35 = load[%64#2] %1#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load7"} : <i7>, <i32>, <i7>, <i32>
    %73 = addi %dataResult_35, %72 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i32>
    %addressResult_36, %dataResult_37 = store[%64#1] %73 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store8"} : <i7>, <i32>, <i7>, <i32>
    %74 = addi %59, %60 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i9>
    %75:2 = fork [2] %74 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i9>
    %76 = cmpi ult, %75#1, %67 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i9>
    %77:4 = fork [4] %76 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_38, %falseResult_39 = cond_br %77#0, %75#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i9>
    %78 = trunci %trueResult_38 {handshake.bb = 4 : ui32, handshake.name = "trunci4"} : <i9> to <i8>
    %trueResult_40, %falseResult_41 = cond_br %77#3, %64#3 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i7>
    %trueResult_42, %falseResult_43 = cond_br %77#2, %66#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i8>
    sink %falseResult_43 {handshake.name = "sink4"} : <i8>
    %trueResult_44, %falseResult_45 = cond_br %77#1, %69#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %79 = merge %falseResult_39 {handshake.bb = 5 : ui32, handshake.name = "merge0"} : <i9>
    %80 = extui %79 {handshake.bb = 5 : ui32, handshake.name = "extui14"} : <i9> to <i10>
    %81 = merge %falseResult_41 {handshake.bb = 5 : ui32, handshake.name = "merge1"} : <i7>
    %82:2 = fork [2] %81 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i7>
    %83 = extui %82#0 {handshake.bb = 5 : ui32, handshake.name = "extui15"} : <i7> to <i10>
    %84 = extui %82#1 {handshake.bb = 5 : ui32, handshake.name = "extui16"} : <i7> to <i8>
    %85 = constant %86 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 1 : i8} : <>, <i8>
    %result_46, %index_47 = control_merge [%falseResult_45]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_47 {handshake.name = "sink5"} : <i1>
    %86 = source {handshake.bb = 5 : ui32, handshake.name = "source5"} : <>
    %87 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %88 = addi %80, %83 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i10>
    %89 = addi %84, %85 {handshake.bb = 5 : ui32, handshake.name = "addi7"} : <i8>
    %90:2 = fork [2] %89 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i8>
    %91 = trunci %90#0 {handshake.bb = 5 : ui32, handshake.name = "trunci5"} : <i8> to <i7>
    %92 = constant %87 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 100 : i8} : <>, <i8>
    %93 = cmpi ult, %90#1, %92 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i8>
    %94:3 = fork [3] %93 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i1>
    %trueResult_48, %falseResult_49 = cond_br %94#1, %91 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i7>
    sink %falseResult_49 {handshake.name = "sink6"} : <i7>
    %trueResult_50, %falseResult_51 = cond_br %94#2, %result_46 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %trueResult_52, %falseResult_53 = cond_br %94#0, %88 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <i10>
    sink %trueResult_52 {handshake.name = "sink7"} : <i10>
    %95 = merge %falseResult_53 {handshake.bb = 6 : ui32, handshake.name = "merge2"} : <i10>
    %96 = extui %95 {handshake.bb = 6 : ui32, handshake.name = "extui17"} : <i10> to <i32>
    %result_54, %index_55 = control_merge [%falseResult_51]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_55 {handshake.name = "sink8"} : <i1>
    %97:3 = fork [3] %result_54 {handshake.bb = 6 : ui32, handshake.name = "fork22"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %96, %memEnd_1, %memEnd, %1#2, %0#1 : <i32>, <>, <>, <>, <>
  }
}

