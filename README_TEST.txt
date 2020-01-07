Brief README to run tests on PULP with 8 cores (the 16 core configuration is not suppoerted yet)

1. Fetch the precompiled-SDK and configure it for PULP (no wolf)

   1.1 "make update_pulp_sdk_noethz" from the top of huawei repo

       "make setup_sdk_noethz" from the top of huawei repo

   1.2 ALTERNATIVE:

       run the script "get-sdk-2019.11.03-CentOS_7.py" from sdk-releases folder

       go in the folder where the sdk has been downloader

       run the following commands:

       source env/env-sdk-2019.11.03.sh

       source pkg/sdk/2019.11.03/configs/pulp.sh

       source pkg/sdk/2019.11.03/configs/platform-rtl.sh

  


2. Fetch a parallel test like Matrix Multiplication (works well with "rt" functions)

       git clone https://iis-git.ee.ethz.ch/giuseppe.tagliavini/matrixMul.git
       or through SSH
       git clone git@iis-git.ee.ethz.ch:giuseppe.tagliavini/matrixMul.git

       go in the folder where the app has been downloaded

       run the following commands:

           make clean all (to compile)

           make clean all run (to compile and run on RTL)
   

   
