openriscPipeline {

    yosysReport {
		core 'mor1kx'
		target 'synth'
		logPath 'build/mor1kx_*/synth-icestorm/yosys.log'
	}

    job('verilator') {
        job 'verilator'
    }

    job('icarus-cappuccino') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy'
    }

    job('icarus-cappuccino-dmmu-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy'
        extraCoreArgs '--feature_dmmu NONE'
    }

    job('icarus-cappuccino-immu-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy or1k-dsxinsn'
        extraCoreArgs '--feature_immu NONE'
    }

    job('icarus-cappuccino-datacache-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy'
        extraCoreArgs '--feature_datacache NONE'
    }

    job('icarus-cappuccino-instructioncache-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy'
        extraCoreArgs '--feature_instructioncache NONE'
    }

    job('icarus-cappuccino-debugunit-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy'
        extraCoreArgs '--feature_debugunit NONE'
    }

    job('icarus-cappuccino-cmov-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy or1k-cmov'
        extraCoreArgs '--feature_cmov NONE'
    }

    job('icarus-cappuccino-ext-none') {
        job 'or1k-tests'
        sim 'icarus'
        pipeline 'CAPPUCCINO'
        expectedFailures 'or1k-cy or1k-ext'
        extraCoreArgs '--feature_ext NONE'
    }

//    TODO: Fix failing Job
//
//    job('icarus-espresso') {
//        job 'or1k-tests'
//        sim 'icarus'
//        pipeline 'ESPRESSO'
//    }
}
