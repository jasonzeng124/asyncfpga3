module {
  func.func @kernel_2mm(%arg0: i32 {handshake.arg_name = "alpha"}, %arg1: i32 {handshake.arg_name = "beta"}, %arg2: memref<100xi32> {handshake.arg_name = "tmp"}, %arg3: memref<100xi32> {handshake.arg_name = "A"}, %arg4: memref<100xi32> {handshake.arg_name = "B"}, %arg5: memref<100xi32> {handshake.arg_name = "C"}, %arg6: memref<100xi32> {handshake.arg_name = "D"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %c0_i32_1 = arith.constant {handshake.name = "constant7"} 0 : i32
    %4 = arith.extui %3 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb3(%c0_i32_1, %c0_i32_1 : i32, i32) {handshake.name = "br2"}
  ^bb3(%5: i32, %6: i32):  // 2 preds: ^bb2, ^bb3
    %c10_i32 = arith.constant {handshake.name = "constant8"} 10 : i32
    %c1_i32 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c3_i64 = arith.constant {handshake.name = "constant10"} 3 : i64
    %c1_i64 = arith.constant {handshake.name = "constant11"} 1 : i64
    %7 = arith.extui %5 {handshake.name = "extui3"} : i32 to i64
    %8 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %9 = arith.shli %1, %c3_i64 {handshake.name = "shli1"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi15"} : i64
    %11 = arith.addi %10, %7 {handshake.name = "addi0"} : i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast0"} : i64 to index
    %13 = memref.load %arg3[%12] {handshake.name = "load0"} : memref<100xi32>
    %14 = arith.muli %13, %arg0 {handshake.name = "muli1"} : i32
    %15 = arith.extui %5 {handshake.name = "extui4"} : i32 to i64
    %16 = arith.shli %15, %c1_i64 {handshake.name = "shli2"} : i64
    %17 = arith.shli %15, %c3_i64 {handshake.name = "shli3"} : i64
    %18 = arith.addi %16, %17 {handshake.name = "addi16"} : i64
    %19 = arith.addi %18, %4 {handshake.name = "addi1"} : i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast1"} : i64 to index
    %21 = memref.load %arg4[%20] {handshake.name = "load1"} : memref<100xi32>
    %22 = arith.muli %14, %21 {handshake.name = "muli3"} : i32
    %23 = arith.addi %6, %22 {handshake.name = "addi2"} : i32
    %24 = arith.addi %5, %c1_i32 {handshake.name = "addi3"} : i32
    %25 = arith.cmpi ult, %24, %c10_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %25, ^bb3(%24, %23 : i32, i32), ^bb4(%23 : i32) {handshake.name = "cond_br0"}
  ^bb4(%26: i32):  // pred: ^bb3
    %c10_i32_2 = arith.constant {handshake.name = "constant12"} 10 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant13"} 1 : i32
    %c3_i64_4 = arith.constant {handshake.name = "constant14"} 3 : i64
    %c1_i64_5 = arith.constant {handshake.name = "constant15"} 1 : i64
    %27 = arith.extui %3 {handshake.name = "extui5"} : i32 to i64
    %28 = arith.shli %2, %c1_i64_5 {handshake.name = "shli4"} : i64
    %29 = arith.shli %2, %c3_i64_4 {handshake.name = "shli5"} : i64
    %30 = arith.addi %28, %29 {handshake.name = "addi17"} : i64
    %31 = arith.addi %30, %27 {handshake.name = "addi4"} : i64
    %32 = arith.index_cast %31 {handshake.name = "index_cast2"} : i64 to index
    memref.store %26, %arg2[%32] {handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<100xi32>
    %33 = arith.addi %3, %c1_i32_3 {handshake.name = "addi5"} : i32
    %34 = arith.cmpi ult, %33, %c10_i32_2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %34, ^bb2(%33 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c10_i32_6 = arith.constant {handshake.name = "constant16"} 10 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant17"} 1 : i32
    %c0_i32_8 = arith.constant {handshake.name = "constant18"} 0 : i32
    %35 = arith.addi %0, %c1_i32_7 {handshake.name = "addi6"} : i32
    %36 = arith.cmpi ult, %35, %c10_i32_6 {handshake.name = "cmpi2"} : i32
    cf.cond_br %36, ^bb1(%35 : i32), ^bb6(%c0_i32_8 : i32) {handshake.name = "cond_br2"}
  ^bb6(%37: i32):  // 2 preds: ^bb5, ^bb10
    %c0_i32_9 = arith.constant {handshake.name = "constant19"} 0 : i32
    %38 = arith.extui %37 {handshake.name = "extui6"} : i32 to i64
    %39 = arith.extui %37 {handshake.name = "extui7"} : i32 to i64
    %40 = arith.extui %37 {handshake.name = "extui8"} : i32 to i64
    cf.br ^bb7(%c0_i32_9 : i32) {handshake.name = "br3"}
  ^bb7(%41: i32):  // 2 preds: ^bb6, ^bb9
    %c0_i32_10 = arith.constant {handshake.name = "constant20"} 0 : i32
    %c3_i64_11 = arith.constant {handshake.name = "constant21"} 3 : i64
    %c1_i64_12 = arith.constant {handshake.name = "constant22"} 1 : i64
    %42 = arith.extui %41 {handshake.name = "extui9"} : i32 to i64
    %43 = arith.shli %38, %c1_i64_12 {handshake.name = "shli6"} : i64
    %44 = arith.shli %38, %c3_i64_11 {handshake.name = "shli7"} : i64
    %45 = arith.addi %43, %44 {handshake.name = "addi18"} : i64
    %46 = arith.addi %45, %42 {handshake.name = "addi7"} : i64
    %47 = arith.index_cast %46 {handshake.name = "index_cast3"} : i64 to index
    %48 = memref.load %arg6[%47] {handshake.name = "load3"} : memref<100xi32>
    %49 = arith.muli %48, %arg1 {handshake.name = "muli6"} : i32
    %50 = arith.extui %41 {handshake.name = "extui10"} : i32 to i64
    cf.br ^bb8(%c0_i32_10, %49 : i32, i32) {handshake.name = "br4"}
  ^bb8(%51: i32, %52: i32):  // 2 preds: ^bb7, ^bb8
    %c10_i32_13 = arith.constant {handshake.name = "constant23"} 10 : i32
    %c1_i32_14 = arith.constant {handshake.name = "constant24"} 1 : i32
    %c3_i64_15 = arith.constant {handshake.name = "constant25"} 3 : i64
    %c1_i64_16 = arith.constant {handshake.name = "constant26"} 1 : i64
    %53 = arith.extui %51 {handshake.name = "extui11"} : i32 to i64
    %54 = arith.shli %39, %c1_i64_16 {handshake.name = "shli8"} : i64
    %55 = arith.shli %39, %c3_i64_15 {handshake.name = "shli9"} : i64
    %56 = arith.addi %54, %55 {handshake.name = "addi19"} : i64
    %57 = arith.addi %56, %53 {handshake.name = "addi8"} : i64
    %58 = arith.index_cast %57 {handshake.name = "index_cast4"} : i64 to index
    %59 = memref.load %arg2[%58] {handshake.name = "load4"} : memref<100xi32>
    %60 = arith.extui %51 {handshake.name = "extui12"} : i32 to i64
    %61 = arith.shli %60, %c1_i64_16 {handshake.name = "shli10"} : i64
    %62 = arith.shli %60, %c3_i64_15 {handshake.name = "shli11"} : i64
    %63 = arith.addi %61, %62 {handshake.name = "addi20"} : i64
    %64 = arith.addi %63, %50 {handshake.name = "addi9"} : i64
    %65 = arith.index_cast %64 {handshake.name = "index_cast5"} : i64 to index
    %66 = memref.load %arg5[%65] {handshake.name = "load5"} : memref<100xi32>
    %67 = arith.muli %59, %66 {handshake.name = "muli9"} : i32
    %68 = arith.addi %52, %67 {handshake.name = "addi10"} : i32
    %69 = arith.addi %51, %c1_i32_14 {handshake.name = "addi11"} : i32
    %70 = arith.cmpi ult, %69, %c10_i32_13 {handshake.name = "cmpi3"} : i32
    cf.cond_br %70, ^bb8(%69, %68 : i32, i32), ^bb9(%68 : i32) {handshake.name = "cond_br3"}
  ^bb9(%71: i32):  // pred: ^bb8
    %c10_i32_17 = arith.constant {handshake.name = "constant27"} 10 : i32
    %c1_i32_18 = arith.constant {handshake.name = "constant28"} 1 : i32
    %c3_i64_19 = arith.constant {handshake.name = "constant29"} 3 : i64
    %c1_i64_20 = arith.constant {handshake.name = "constant30"} 1 : i64
    %72 = arith.extui %41 {handshake.name = "extui13"} : i32 to i64
    %73 = arith.shli %40, %c1_i64_20 {handshake.name = "shli12"} : i64
    %74 = arith.shli %40, %c3_i64_19 {handshake.name = "shli13"} : i64
    %75 = arith.addi %73, %74 {handshake.name = "addi21"} : i64
    %76 = arith.addi %75, %72 {handshake.name = "addi12"} : i64
    %77 = arith.index_cast %76 {handshake.name = "index_cast6"} : i64 to index
    memref.store %71, %arg6[%77] {handshake.name = "store6"} : memref<100xi32>
    %78 = arith.addi %41, %c1_i32_18 {handshake.name = "addi13"} : i32
    %79 = arith.cmpi ult, %78, %c10_i32_17 {handshake.name = "cmpi4"} : i32
    cf.cond_br %79, ^bb7(%78 : i32), ^bb10 {handshake.name = "cond_br4"}
  ^bb10:  // pred: ^bb9
    %c10_i32_21 = arith.constant {handshake.name = "constant31"} 10 : i32
    %c1_i32_22 = arith.constant {handshake.name = "constant32"} 1 : i32
    %80 = arith.addi %37, %c1_i32_22 {handshake.name = "addi14"} : i32
    %81 = arith.cmpi ult, %80, %c10_i32_21 {handshake.name = "cmpi5"} : i32
    cf.cond_br %81, ^bb6(%80 : i32), ^bb11 {handshake.name = "cond_br5"}
  ^bb11:  // pred: ^bb10
    return {handshake.name = "return0"}
  }
}

