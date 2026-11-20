module {
  handshake.func @spmv(%arg0: !handshake.channel<i32>, %arg1: memref<11xi32>, %arg2: memref<10xi32>, %arg3: memref<10xi32>, %arg4: memref<10xi32>, %arg5: memref<10xi32>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["n", "row", "col", "val", "vec", "out", "row_start", "col_start", "val_start", "vec_start", "out_start", "start"], resNames = ["out0", "row_end", "col_end", "val_end", "vec_end", "out_end", "end"]} {
    %0:4 = fork [4] %arg11 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %memEnd = mem_controller[%arg5 : memref<10xi32>] %arg10 (%55, %addressResult_49, %dataResult_50) %63#4 {connectedBlocks = [3 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i32>, !handshake.channel<i4>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg4 : memref<10xi32>] %arg9 (%addressResult_31) %63#3 {connectedBlocks = [2 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg3 : memref<10xi32>] %arg8 (%addressResult_27) %63#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg2 : memref<10xi32>] %arg7 (%addressResult_29) %63#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller8"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_5:2, %memEnd_6 = mem_controller[%arg1 : memref<11xi32>] %arg6 (%addressResult, %addressResult_11) %63#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller9"} :    (!handshake.channel<i4>, !handshake.channel<i4>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:3 = fork [3] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    %6 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %trueResult_7, %falseResult_8 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_8 {handshake.name = "sink0"} : <i32>
    %trueResult_9, %falseResult_10 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %8 = mux %14#0 [%7, %trueResult_51] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i4>
    %11 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 1 : i4} : <>, <i4>
    %12 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i4>
    %13 = mux %14#1 [%trueResult_7, %trueResult_53] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_9, %trueResult_55]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %15:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %addressResult, %dataResult = load[%12] %outputs_5#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i4>, <i32>, <i4>, <i32>
    %17:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %18 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i4>
    %addressResult_11, %dataResult_12 = load[%18] %outputs_5#1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i4>, <i32>, <i4>, <i32>
    %19:2 = fork [2] %dataResult_12 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %20 = cmpi slt, %17#0, %19#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %21:6 = fork [6] %20 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_13, %falseResult_14 = cond_br %21#5, %17#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %22:2 = fork [2] %trueResult_13 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %23 = constant %15#0 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = false} : <>, <i1>
    %trueResult_15, %falseResult_16 = cond_br %21#0, %23 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i1>
    %24 = extui %falseResult_16 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %25 = extui %trueResult_15 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i1> to <i32>
    %trueResult_17, %falseResult_18 = cond_br %21#4, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %21#3, %9#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_21, %falseResult_22 = cond_br %21#2, %19#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    sink %falseResult_22 {handshake.name = "sink1"} : <i32>
    %trueResult_23, %falseResult_24 = cond_br %21#1, %15#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %26 = mux %36#0 [%22#1, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %27:3 = fork [3] %26 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i32>
    %28 = trunci %27#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i4>
    %29 = trunci %27#1 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i4>
    %30 = mux %36#1 [%25, %trueResult_35] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %36#2 [%trueResult_17, %trueResult_37] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %32 = mux %36#3 [%trueResult_19, %trueResult_39] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %36#4 [%22#0, %trueResult_41] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %34 = mux %36#5 [%trueResult_21, %trueResult_43] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %35:2 = fork [2] %34 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i32>
    %result_25, %index_26 = control_merge [%trueResult_23, %trueResult_45]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %36:6 = fork [6] %index_26 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i1>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %38 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %addressResult_27, %dataResult_28 = load[%29] %outputs_1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i4>, <i32>, <i4>, <i32>
    %addressResult_29, %dataResult_30 = load[%28] %outputs_3 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i4>, <i32>, <i4>, <i32>
    %39 = trunci %dataResult_30 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i32> to <i4>
    %addressResult_31, %dataResult_32 = load[%39] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i4>, <i32>, <i4>, <i32>
    %40 = muli %dataResult_28, %dataResult_32 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %41 = addi %30, %40 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %42 = addi %27#2, %38 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %43:2 = fork [2] %42 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i32>
    %44 = cmpi ne, %43#1, %35#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %45:7 = fork [7] %44 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_33, %falseResult_34 = cond_br %45#6, %43#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %falseResult_34 {handshake.name = "sink2"} : <i32>
    %trueResult_35, %falseResult_36 = cond_br %45#5, %41 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_37, %falseResult_38 = cond_br %45#4, %31 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_39, %falseResult_40 = cond_br %45#3, %32 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_41, %falseResult_42 = cond_br %45#2, %33 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_43, %falseResult_44 = cond_br %45#1, %35#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    sink %falseResult_44 {handshake.name = "sink3"} : <i32>
    %trueResult_45, %falseResult_46 = cond_br %45#0, %result_25 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %46 = mux %53#0 [%24, %falseResult_36] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %47 = mux %53#1 [%falseResult_18, %falseResult_38] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i32>
    %49 = mux %53#2 [%falseResult_20, %falseResult_40] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %50:2 = fork [2] %49 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i32>
    %51 = trunci %50#0 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i32> to <i4>
    %52 = mux %53#3 [%falseResult_14, %falseResult_42] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %result_47, %index_48 = control_merge [%falseResult_24, %falseResult_46]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %53:4 = fork [4] %index_48 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i1>
    %54:2 = fork [2] %result_47 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <>
    %55 = constant %54#0 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %56 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %57 = constant %56 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %addressResult_49, %dataResult_50 = store[%51] %46 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store5"} : <i4>, <i32>, <i4>, <i32>
    %58 = addi %50#1, %57 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %59:2 = fork [2] %58 {handshake.bb = 3 : ui32, handshake.name = "fork19"} : <i32>
    %60 = cmpi ne, %59#1, %48#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %61:4 = fork [4] %60 {handshake.bb = 3 : ui32, handshake.name = "fork20"} : <i1>
    %trueResult_51, %falseResult_52 = cond_br %61#3, %59#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    sink %falseResult_52 {handshake.name = "sink4"} : <i32>
    %trueResult_53, %falseResult_54 = cond_br %61#2, %48#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    sink %falseResult_54 {handshake.name = "sink5"} : <i32>
    %trueResult_55, %falseResult_56 = cond_br %61#1, %54#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <>
    %trueResult_57, %falseResult_58 = cond_br %61#0, %52 {handshake.bb = 3 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    sink %trueResult_57 {handshake.name = "sink6"} : <i32>
    %62 = mux %index_60 [%6, %falseResult_58] {handshake.bb = 4 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_59, %index_60 = control_merge [%falseResult_10, %falseResult_56]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %63:5 = fork [5] %result_59 {handshake.bb = 4 : ui32, handshake.name = "fork21"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %62, %memEnd_6, %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %0#1 : <i32>, <>, <>, <>, <>, <>, <>
  }
}

