using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class VertexComparer : IEqualityComparer<MapsVertex>
    {
        public bool Equals(MapsVertex v1, MapsVertex v2)
        {

            if (v1.agent != v2.agent)
                throw new Exception();
            foreach (var kv in v1.stateIndexes)
            {
                if (!kv.Key.Equals(v1.agent))
                {
                    if (!v2.stateIndexes.ContainsKey(kv.Key) || !v2.stateIndexes[kv.Key].Equals(kv.Value))
                        return false;
                }
            }
            if (v1.publicFacts.Count != v2.publicFacts.Count)
                return false;
            foreach (GroundedPredicate p in v1.publicFacts)
                if (!v2.publicFacts.Contains(p))
                    return false;

            return true;



        }


        public int GetHashCode(MapsVertex v)
        {
            int code = 0;
            foreach (var kv in v.stateIndexes)
            {
                if (!kv.Key.Equals(v.agent))
                    code += kv.Key.GetHashCode() + kv.Value.GetHashCode();
            }
            foreach (GroundedPredicate gp in v.publicFacts)
            {
                code += gp.GetHashCode();
            }
            return code;
        }
    }
}
