#include "blimit.hpp"

unsigned int bvalue(unsigned int method, unsigned long node_id) {

    return(((method+1)*node_id + 7) % 100);
}
