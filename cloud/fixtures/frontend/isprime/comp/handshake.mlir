module {
  handshake.func @isprime(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %2 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %3 = cmpi slt, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %4 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 4 : i32} : <>, <i32>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 2 : i32} : <>, <i32>
    %9 = cmpi slt, %4, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %9, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %9, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %9, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %9, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %10 = merge %falseResult_67 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %11 = merge %falseResult_69 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_12, %index_13 = control_merge [%falseResult_65]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %12 = constant %result_12 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %13 = muli %10, %10 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %14 = cmpi sgt, %13, %11 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %14, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %14, %result_12 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %trueResult_18, %falseResult_19 = cond_br %14, %10 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %14, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %15 = mux %index_23 [%falseResult_9, %falseResult_19] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_23 [%falseResult_11, %falseResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result_22, %index_23 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %17 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %18 = constant %17 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %19 = shrsi %16, %18 {handshake.bb = 3 : ui32, handshake.name = "shrsi0"} : <i32>
    %20 = br %15 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <i32>
    %21 = br %16 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <i32>
    %22 = br %19 {handshake.bb = 3 : ui32, handshake.name = "br3"} : <i32>
    %23 = br %result_22 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <>
    %24 = mux %index_25 [%20, %falseResult_35] {handshake.bb = 4 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %index_25 [%21, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_25 [%20, %falseResult_31] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_25 [%22, %falseResult_37] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_24, %index_25 = control_merge [%23, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %28 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %29 = constant %28 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %30 = cmpi sgt, %24, %27 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %31 = shli %24, %29 {handshake.bb = 4 : ui32, handshake.name = "shli0"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %30, %24 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %30, %25 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %30, %26 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %30, %result_24 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <>
    %trueResult_34, %falseResult_35 = cond_br %30, %31 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %30, %27 {handshake.bb = 4 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %32 = merge %trueResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %33 = merge %trueResult_28 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %34 = merge %trueResult_30 {handshake.bb = 5 : ui32, handshake.name = "merge5"} : <i32>
    %result_38, %index_39 = control_merge [%trueResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %35 = cmpi slt, %32, %34 {handshake.bb = 5 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %35, %33 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %35, %34 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %35, %result_38 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <>
    %trueResult_46, %falseResult_47 = cond_br %35, %32 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %36 = mux %index_49 [%falseResult_47, %falseResult_59] {handshake.bb = 6 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %37 = mux %index_49 [%falseResult_41, %falseResult_51] {handshake.bb = 6 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %38 = mux %index_49 [%falseResult_41, %falseResult_53] {handshake.bb = 6 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %39 = mux %index_49 [%falseResult_43, %falseResult_55] {handshake.bb = 6 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_48, %index_49 = control_merge [%falseResult_45, %falseResult_57]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %40 = source {handshake.bb = 6 : ui32, handshake.name = "source4"} : <>
    %41 = constant %40 {handshake.bb = 6 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %42 = cmpi slt, %37, %36 {handshake.bb = 6 : ui32, handshake.name = "cmpi5"} : <i32>
    %43 = subi %37, %36 {handshake.bb = 6 : ui32, handshake.name = "subi0"} : <i32>
    %44 = select %42[%37, %43] {handshake.bb = 6 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %45 = shrsi %36, %41 {handshake.bb = 6 : ui32, handshake.name = "shrsi1"} : <i32>
    %46 = cmpi slt, %45, %39 {handshake.bb = 6 : ui32, handshake.name = "cmpi6"} : <i32>
    %trueResult_50, %falseResult_51 = cond_br %46, %44 {handshake.bb = 6 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %46, %38 {handshake.bb = 6 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %46, %39 {handshake.bb = 6 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_56, %falseResult_57 = cond_br %46, %result_48 {handshake.bb = 6 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %trueResult_58, %falseResult_59 = cond_br %46, %45 {handshake.bb = 6 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %47 = mux %index_61 [%trueResult_40, %trueResult_50] {handshake.bb = 7 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %index_61 [%trueResult_40, %trueResult_52] {handshake.bb = 7 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %49 = mux %index_61 [%trueResult_42, %trueResult_54] {handshake.bb = 7 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_60, %index_61 = control_merge [%trueResult_44, %trueResult_56]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %50 = constant %result_60 {handshake.bb = 7 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %51 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %52 = constant %51 {handshake.bb = 7 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %53 = cmpi eq, %47, %50 {handshake.bb = 7 : ui32, handshake.name = "cmpi7"} : <i32>
    %54 = addi %49, %52 {handshake.bb = 7 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult_62, %falseResult_63 = cond_br %53, %50 {handshake.bb = 7 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %53, %result_60 {handshake.bb = 7 : ui32, handshake.name = "cond_br34"} : <i1>, <>
    %trueResult_66, %falseResult_67 = cond_br %53, %54 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_68, %falseResult_69 = cond_br %53, %48 {handshake.bb = 7 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %55 = mux %index_71 [%trueResult, %trueResult_4, %trueResult_14, %trueResult_62] {handshake.bb = 8 : ui32, handshake.name = "mux13"} : <i2>, [<i32>, <i32>, <i32>, <i32>] to <i32>
    %result_70, %index_71 = control_merge [%trueResult_0, %trueResult_6, %trueResult_16, %trueResult_64]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>, <>, <>] to <>, <i2>
    end {handshake.bb = 8 : ui32, handshake.name = "end0"} %55, %arg1 : <i32>, <>
  }
}

