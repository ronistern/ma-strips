using System.Collections.Generic;

namespace Planning
{
    class Action_Evaluation
    {
        public double grade = -1;
        public Dictionary<string, List<Landmark>> agentLandmarks = null;
        public Action_Evaluation()
        {
            agentLandmarks = new Dictionary<string, List<Landmark>>();
        }
    }
}
