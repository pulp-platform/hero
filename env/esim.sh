THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

# FIXME: this should not be based on the genesys2 execution environment
source ${THIS_DIR}/ediggenesys2.sh
export PULP_CURRENT_CONFIG=hero-sim@config_file=${HERO_PULP_SDK_DIR}/configs/json/hero-urania.json
