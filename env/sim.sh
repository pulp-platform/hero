THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

source ${THIS_DIR}/urania.sh
export PULP_CURRENT_CONFIG=hero-sim@config_file=/scratch/msc19f8/workspace/hero-v3/support/pulp-sdk/configs/json/hero-urania.json
