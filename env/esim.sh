THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

source ${THIS_DIR}/ehuawei-sdk.sh
export PULP_CURRENT_CONFIG=hero-sim@config_file=${HERO_PULP_SDK_DIR}/configs/json/hero-huawei.json
