pipeline {
    agent any

    environment{
        JOB= '$JOB'
        SIM= '$SIM'
        PIPELINE= '$PIPELINE'
        EXPECTED_FAILURES= '$EXPECTED_FAILURES'
        EXTRA_CORE_ARGS= '$EXTRA_CORE_ARGS'
    }
    stages {
        stage('Build') {
            steps {
                sh 'docker pull librecores/librecores-ci:0.2.0'
                sh 'docker images'
            }
        }
        stage('Run') {
            steps {
                sh 'docker run --rm -v $(pwd):/src -e JOB -e SIM -e PIPELINE -e EXPECTED_FAILURES -e EXTRA_CORE_ARGS librecores/librecores-ci /src/.travis/test.sh'
            }
        }
        stage('run-parallel-jobs') {
            steps {
                parallel(
                    verilator:{
                        export $JOB='verilator'
                    }
                    testing:{  
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy"
                    },
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy" $EXTRA_CORE_ARGS="--feature_dmmu NONE"
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy or1k-dsxinsn" $EXTRA_CORE_ARGS="--feature_immu NONE"
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy" $EXTRA_CORE_ARGS="--feature_datacache NONE" 
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy" $EXTRA_CORE_ARGS="--feature_instructioncache NONE"
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy" $EXTRA_CORE_ARGS="--feature_debugunit NONE"
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy or1k-cmov" EXTRA_CORE_ARGS="--feature_cmov NONE"
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='CAPPUCCINO' $EXPECTED_FAILURES="or1k-cy or1k-ext" EXTRA_CORE_ARGS="--feature_ext NONE"
                    }
                    testing:{
                        export $JOB='or1k-tests' $SIM='icarus' $PIPELINE='ESPRESSO'
                    }
                    )
            }
        }
    }
}