using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;

namespace Planning
{
    public class Domain
    {
        public static Dictionary<string, string> MapGroundedActionNamesToOutputNames = null;

        public static void ResetStaticVar()
        {
            MapGroundedActionNamesToOutputNames = new Dictionary<string, string>();
        }

        public string Name { get; protected set; }
        public List<string> Types { get; private set; }
        public Dictionary<string, string> TypeHierarchy { get; private set; }
        public List<Action> Actions { get; set; }
        public HashSet<Action> PrivateActions { get; set; }
        public HashSet<Action> PublicActions { get; set; }
        public HashSet<Constant> Constants { get; protected set; }
        public HashSet<Constant> PrivateConstants { get; protected set; }
        public HashSet<Constant> PublicConstants { get; protected set; }
        private Dictionary<string, string> m_dConstantNameToType = new Dictionary<string, string>();
        public Dictionary<string, string> ConstantNameToType { get { return m_dConstantNameToType; } }
        public HashSet<Predicate> Predicates { get;  set; }
        public HashSet<Predicate> PrivatePredicates { get; protected set; }
        public HashSet<Predicate> PublicPredicates { get; protected set; }
        public List<string> Functions { get; protected set; }
        public List<string> m_lAlwaysKnown { get; protected set; }
        public List<string> m_lAlwaysConstant { get; protected set; }
        private List<string> m_lObservable;
        public string Path { get; private set; }
        public Dictionary<string, Action> mapActionNameToAction = null;
        public bool m_bUseOptions = true;
        public bool m_bReplaceNonDeterministicEffectsWithOptions = true;
        public bool UseCosts { get; private set; }
        public List<Action> groundedAction = null;
        public const string OPTION = "OPTION_TYPE";
        public const string OPTION_PREDICATE = "option";
        public const string VALUE = "VALUE_TYPE";
        public const string VALUE_PARAMETER = "?V_PARAM";
        public const string TAG = "TAG_TYPE";
        public const string TAG_PARAMETER = "?TAG_PARAM";
        public const string TRUE_VALUE = "V_TRUE";
        public const string FALSE_VALUE = "V_FALSE";
        public const string TRUE_PREDICATE = "P_TRUE";
        public const string FALSE_PREDICATE = "P_FALSE";
        public const string ARTIFICIAL_PREDICATE = "P_ARTIFICIAL";

        public const int TIME_STEPS = 0;
        public const int MAX_OPTIONS = 3;


        public bool RemoveConflictingConditionalEffects = false;
        private Dictionary<Predicate, Predicate> m_dAuxilaryPredicates;


        public Domain(string sName, string sPath)
        {
            UseCosts = true;
            Name = sName;
            Path = sPath;
            Actions = new List<Action>();
            Constants = new HashSet<Constant>();
            PublicConstants = new HashSet<Constant>();
            PrivateConstants = new HashSet<Constant>();
            Predicates = new HashSet<Predicate>();
            PrivatePredicates = new HashSet<Predicate>();
            PublicPredicates = new HashSet<Predicate>();
            Types = new List<string>();
            TypeHierarchy = new Dictionary<string, string>();
            m_lAlwaysKnown = new List<string>();
            m_lAlwaysKnown.Add("increase");
            m_lAlwaysKnown.Add("decrease");
            m_lAlwaysKnown.Add("=");
            m_lAlwaysConstant = new List<string>();
            m_lObservable = new List<string>();
            m_dAuxilaryPredicates = new Dictionary<Predicate, Predicate>();
            Functions = new List<string>();
        }


        public Domain Clone()
        {
            Domain d = new Domain(Name, Path);
            d.UseCosts = UseCosts;
            d.Actions = new List<Action>(Actions);
            d.Constants = new HashSet<Constant>(Constants);
            d.PublicConstants = new HashSet<Constant>(PublicConstants);
            d.PrivateConstants = new HashSet<Constant>(PrivateConstants);
            d.Predicates = new HashSet<Predicate>(Predicates);
            d.PrivatePredicates = new HashSet<Predicate>(PrivatePredicates);
            d.PublicPredicates = new HashSet<Predicate>(PublicPredicates);
            d.Types = new List<string>(Types);
            d.TypeHierarchy = new Dictionary<string, string>(TypeHierarchy);
            d.m_lAlwaysKnown = new List<string>(m_lAlwaysKnown);
            d.m_lAlwaysConstant = new List<string>(m_lAlwaysConstant);
            d.m_lObservable = new List<string>(m_lObservable);
            d.m_dAuxilaryPredicates = new Dictionary<Predicate, Predicate>(m_dAuxilaryPredicates);
            d.Functions = new List<string>(Functions);
            return d;
        }

        public void AddAction(Action a)
        {
            Actions.Add(a);
            if (a.Effects != null)
            {
                HashSet<Predicate> lConditionalEffects = new HashSet<Predicate>();
                HashSet<Predicate> lNonConditionalEffects = new HashSet<Predicate>();

                a.Effects.GetAllEffectPredicates(lConditionalEffects, lNonConditionalEffects);

                foreach (Predicate p in lConditionalEffects)
                {
                    m_lAlwaysKnown.Remove(p.Name);
                    m_lAlwaysConstant.Remove(p.Name);
                }
                foreach (Predicate p in lNonConditionalEffects)
                {
                    m_lAlwaysConstant.Remove(p.Name);
                }
                List<Predicate> lNonDetEffects = a.GetNonDeterministicEffects();
                if (lNonDetEffects != null)
                {
                    foreach (Predicate p in lNonDetEffects)
                    {
                        m_lAlwaysKnown.Remove(p.Name);
                    }
                }

            }
            else if (a.Effects is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)a.Effects).Predicate;
                m_lAlwaysConstant.Remove(p.Name);
            }
            if (a.Observe != null)
            {
                foreach(Predicate p in a.Observe.GetAllPredicates())
                    m_lObservable.Add(p.Name);
            }
        }
        public void AddPublicConstant(Constant c)
        {
            PublicConstants.Add(c);
            m_dConstantNameToType[c.Name] = c.Type;
            Constants.Add(c);
        }
        public void AddPrivateConstant(Constant c)
        {
            PrivateConstants.Add(c);
            m_dConstantNameToType[c.Name] = c.Type;
            Constants.Add(c);
        }
        public void AddPublicPredicate(Predicate p)
        {
            Predicates.Add(p);
            PublicPredicates.Add(p);
            m_lAlwaysKnown.Add(p.Name);
            m_lAlwaysConstant.Add(p.Name);
        }
        public void AddPrivatePredicate(Predicate p)
        {
            Predicates.Add(p);
            PrivatePredicates.Add(p);
            m_lAlwaysKnown.Add(p.Name);
            m_lAlwaysConstant.Add(p.Name);
        }
        public override string ToString()
        {
            string s = "(domain " + Name + "\n";
            s += "(constants " + Parser.ListToString(Constants.ToList()) + ")\n";
            s += "(predicates " + Parser.ListToString(Predicates.ToList()) + ")\n";
            s += "(actions " + Parser.ListToString(Actions) + ")\n";
            s += ")";
            return s;
        }
       
        public void CleanActionList(Problem p)
        {
            HashSet<GroundedPredicate> set = new HashSet<GroundedPredicate>();
            HashSet<Action> pAction = new HashSet<Action>();
            bool flag = true;

            foreach (GroundedPredicate gp in p.Known)
            {
                set.Add(gp);
            }


            while (flag)
            {
                flag = false;

                foreach (Action act in groundedAction)
                {
                    if (!pAction.Contains(act))
                    {
                        if (Contains(set, act.HashPrecondition))
                        {
                            foreach (GroundedPredicate gp in act.HashEffects)
                            {
                                if (!set.Contains(gp))
                                {
                                    flag = true;
                                    set.Add(gp);
                                }
                            }

                            pAction.Add(act);
                        }
                    }
                }

            }
            groundedAction = pAction.ToList();
        }
        private bool Contains(HashSet<GroundedPredicate> x, List<Predicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.Contains(gP)) return false;
            }
            return true;
        }
        //not really checking everything - need to check compatible parameters, constants and so forth
        public bool ContainsPredicate(string sName)
        {
            foreach (Predicate p in Predicates)
                if (p.Name == sName)
                    return true;
            return false;
        }

        public Constant GetConstant(string sName)
        {
            foreach(Constant c in Constants)
                if(c.Name == sName)
                    return c;
            return null;
        }

        public void WriteKnowledgeDomain(string sFileName, Problem p)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain K" + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WriteKnowledgePredicates(sw);
            sw.WriteLine();
            WriteKnowledgeActions(sw);
            p.WriteReasoningActions(sw);
            sw.WriteLine(")");
            sw.Close();
        }

        
        //know whether - no s_0
        public void WriteTaggedDomainNoState(string sFileName, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            if (HasNonDeterministicActions() && m_bUseOptions)
            {
                Domain dDeterministic = RemoveNonDeterministicEffects();
                dDeterministic.WriteTaggedDomainNoState(sFileName, dTags, pCurrent); 
                return;
            }


            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain K" + Name + ")");
            
            
            sw.WriteLine("(:requirements :strips :typing)");
            
            WriteFunctions(sw);
            WriteTypes(sw, true);
            WriteConstants(sw, dTags);
            sw.WriteLine();
            if (SDRPlanner.SplitConditionalEffects)
            {
                List<Predicate> lAdditionalPredicates = new List<Predicate>();
                List<Action> lAllActions = GetKnowledgeActionsNoState(sw, dTags, lAdditionalPredicates);
                WriteTaggedPredicatesNoState(sw, lAdditionalPredicates);
                foreach (Action aKnowWhether in lAllActions)
                    WriteConditionalAction(sw, aKnowWhether);
                sw.WriteLine();
                
                //WriteReasoningActionsNoState(sw, dTags, pCurrent);
            }
            else
            {
                WriteTaggedPredicatesNoState(sw, null);
                sw.WriteLine();
                WriteKnowledgeActionsNoState(sw, dTags);
                //WriteReasoningActionsNoState(sw, dTags, pCurrent);
            }


            sw.WriteLine(")");
            sw.Close();
        }

        public MemoryStream WriteTaggedDomain(string sFileName, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            if (HasNonDeterministicActions() && m_bUseOptions)
            {
                Domain dDeterministic = RemoveNonDeterministicEffects();
                
                return dDeterministic.WriteTaggedDomain(sFileName, dTags, pCurrent);;
            }


            StreamWriter sw = null;
            MemoryStream strStream = new MemoryStream(1000);

            //sw = new StreamWriter(sFileName);
            sw = new StreamWriter(strStream);

            sw.WriteLine("(define (domain K" + Name + ")");


            sw.WriteLine("(:requirements :strips :typing)");

            WriteFunctions(sw);
            WriteTypes(sw, true);
            WriteConstants(sw, dTags);
            sw.WriteLine();


            if (SDRPlanner.SplitConditionalEffects)
            {
                List<Predicate> lAdditionalPredicates = new List<Predicate>();
                List<Action> lAllActions = GetKnowledgeActions(sw, dTags, lAdditionalPredicates);
                WriteTaggedPredicates(sw, lAdditionalPredicates);
                foreach (Action aKnowWhether in lAllActions)
                    WriteConditionalAction(sw, aKnowWhether);
                sw.WriteLine();

                WriteReasoningActions(sw, dTags, pCurrent);
            }
            else
            {
                WriteTaggedPredicates(sw, null);
                sw.WriteLine();
                WriteKnowledgeActions(sw, dTags);
                WriteReasoningActions(sw, dTags, pCurrent);
            }




            if (RemoveConflictingConditionalEffects)
                WriteAxiomsActions(sw, dTags);

            sw.WriteLine(")");
            sw.Flush();
            //sw.Close();//shouldn't close the mem stream
           
                strStream.Position = 0;
                TextReader sr = new StreamReader(strStream, Encoding.ASCII);
                StreamWriter swFile = new StreamWriter(sFileName);
                swFile.Write(sr.ReadToEnd());
                swFile.Close();
            
            return strStream;
        }
        public MemoryStream WriteSimpleDomain()
        {
            MemoryStream ms = new MemoryStream();

            StreamWriter sw = new StreamWriter(ms);
            sw.WriteLine("(define (domain " + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw);
            sw.WriteLine();
            WriteActions(sw, false);
            sw.WriteLine(")");
            sw.Flush();
            ms.Flush();

            return new MemoryStream(ms.ToArray());
        }
        private void WriteFunctions(StreamWriter sw)
        {
            if (Functions.Count > 0)
            {
                sw.Write("(:functions");
                foreach (string sFunction in Functions)
                    sw.Write(" " + sFunction);
                sw.WriteLine(")");

            }
        }

        private Domain RemoveNonDeterministicEffects()
        {
            Domain dDeterministic = new Domain(Name, Path);
            dDeterministic.Predicates = new HashSet<Predicate>(Predicates);
            dDeterministic.Constants = new HashSet<Constant>(Constants);
            dDeterministic.Types = new List<string>(Types);
            dDeterministic.Actions = new List<Action>();
            dDeterministic.m_lAlwaysKnown = m_lAlwaysKnown;
            dDeterministic.m_lAlwaysConstant = m_lAlwaysConstant;
            dDeterministic.m_dConstantNameToType = m_dConstantNameToType;
            dDeterministic.Functions = Functions;

            dDeterministic.Types.Add(Domain.OPTION);
            dDeterministic.m_lAlwaysConstant.Add(Domain.OPTION_PREDICATE);
            //dDeterministic.m_lAlwaysKnown.Add(Domain.OPTION_PREDICATE);

            ParametrizedPredicate ppOption = new ParametrizedPredicate(Domain.OPTION_PREDICATE);
            ppOption.AddParameter(new Parameter(OPTION, "?o"));
            dDeterministic.Predicates.Add(ppOption);

            int cOptions = Math.Max(MaxNonDeterministicEffects(), MAX_OPTIONS);
            for (int iOption = 0; iOption < cOptions; iOption++)
            {
                dDeterministic.Constants.Add(new Constant(OPTION, "opt" + iOption));
            }

            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    Action aDeterministic = a.ReplaceNonDeterministicEffectsWithOptions(m_lAlwaysKnown, MAX_OPTIONS);
                    dDeterministic.Actions.Add(aDeterministic);
                }
                else
                {
                    dDeterministic.Actions.Add(a);
                }
            }

            return dDeterministic;
        }

        private string GeneratePredicateAxiom(GroundedPredicate gp, string sPrefix, string sAdditionalConstants)
        {
            string sGiven = "(Not-" + sPrefix + gp.Name;
            foreach (Constant p in gp.Constants)
                sGiven += " " + p.Name;
            sGiven += sAdditionalConstants;
            sGiven += ")";
            string sEffect = "(and (not " + sGiven + ")";
            sEffect += " (not ";
            sEffect += "(" + sPrefix + gp.Name;
            foreach (Constant p in gp.Constants)
                sEffect += " " + p.Name;
            sEffect += sAdditionalConstants;
            sEffect += ")))";
            string s = "(when " + sGiven + " " + sEffect + ")";
            return s;
        }

        private void WriteAxiomsAction(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            sw.WriteLine("(:action apply-axioms");
            sw.WriteLine("\t:precondition (not (axioms-applied))\n");
            sw.WriteLine("\t:effect (and (axioms-applied)\n");

            HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
            foreach (GroundedPredicate pp in lGrounded)
            {
                sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "", ""));

                if (!AlwaysKnown(pp))
                {
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "K", " " + TRUE_VALUE));
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "K", " " + FALSE_VALUE));

                    foreach (string sTag in dTags.Keys)
                    {
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "KGiven", " " + sTag + " " + TRUE_VALUE));
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "KGiven", " " + sTag + " " + FALSE_VALUE));

                    }
                }
            }
            sw.WriteLine("))");
        }


        private void WriteAxiomsActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {

            HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.WriteLine("(:action apply-axioms-" + gp.Name);
                sw.WriteLine("\t:precondition (not (axioms-applied))");
                sw.WriteLine("\t:effect (and ");

                sw.Write("(axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine(")");


                sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "", ""));

                if (!AlwaysKnown(gp))
                {
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "K", " " + TRUE_VALUE));
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "K", " " + FALSE_VALUE));

                    foreach (string sTag in dTags.Keys)
                    {
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "KGiven", " " + sTag + " " + TRUE_VALUE));
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "KGiven", " " + sTag + " " + FALSE_VALUE));

                    }
                }
                sw.WriteLine("))");
            }
            sw.WriteLine("(:action apply-axioms");
            sw.WriteLine("\t:precondition (and (not (axioms-applied))");
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.Write("\t\t(axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
            sw.WriteLine("\t:effect (and (axioms-applied)");
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.Write("\t\t(not (axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine("))");
            }
            sw.WriteLine("))");

        }

        private void WriteKnowledgePreconditions(StreamWriter sw, Action pa, List<Predicate> lKnow)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            pa.Preconditions.GetAllPredicates(lPredicates);
            CompoundFormula cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(pa.Preconditions.Simplify());

            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    cfAnd.AddOperand(new PredicateFormula(new KnowPredicate(p)));
                }
            }
            sw.WriteLine(":precondition " + cfAnd);

            /*
            sw.Write(":precondition (and");
            foreach (Formula f in cfAnd.Operands)
                sw.Write(" " + f.ToString());
            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    WriteKnowledgePredicate(sw, p);
                }
            }
            
            sw.WriteLine(")");
             * */

        }

        public void WriteKnowledgePredicate(StreamWriter sw, Predicate p)
        {
            if (!AlwaysKnown(p))
                sw.Write(new KnowPredicate(p).ToString());
        }
        private void WriteKnowledgeEffects(StreamWriter sw, Action pa, List<Predicate> lKnow)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            if( pa.Effects != null )
                pa.Effects.GetAllPredicates(lPredicates);
            if( pa.Observe != null )
                pa.Observe.GetAllPredicates(lPredicates);
            CompoundFormula cfAnd = (CompoundFormula)pa.Effects;
            if (cfAnd != null && cfAnd.Operator != "and")
                throw new NotImplementedException();
            sw.Write(":effect (and");
            if (cfAnd != null)
            {
                foreach (Formula f in cfAnd.Operands)
                    sw.Write(" " + f.ToString());
            }
            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    WriteKnowledgePredicate(sw, p);
                }
            }
            sw.WriteLine(")");
        }

        private void WriteKnowledgeAction(StreamWriter sw, Action a)
        {
            sw.WriteLine("(:action " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                WriteKnowledgePreconditions(sw, a, null);
            WriteKnowledgeEffects(sw, a, null);

            sw.WriteLine(")");
            sw.WriteLine();
        }


        private void WriteAction(StreamWriter sw, Action a)
        {
            try
            {
                if (RemoveConflictingConditionalEffects)
                    RemoveConflictingConditionalEffectsFromAction(a);

                sw.WriteLine("(:action " + a.Name);
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    sw.Write(":parameters (");
                    foreach (Parameter p in pa.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }
                if (a.Preconditions != null)
                    sw.WriteLine(":precondition " + a.Preconditions);
                sw.WriteLine(":effect " + a.Effects);

                sw.WriteLine(")");
                sw.WriteLine();
            }
            catch(Exception e)
            {
                Console.WriteLine(e.ToString());
            }
        }

        private void WriteSensor(StreamWriter sw, Action a)
        {
            Debug.Assert(a.Observe != null && a.Effects == null);
            sw.WriteLine("(:sensor " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                sw.WriteLine(":condition " + a.Preconditions);
            sw.WriteLine(":sensed " + a.Observe);

            sw.WriteLine(")");
            sw.WriteLine();
        }

        private void WriteConditionalSplitAction(StreamWriter sw, Action a, List<Predicate> lKnow)
        {
            sw.WriteLine("(:action " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                WriteKnowledgePreconditions(sw, a, lKnow);
            WriteKnowledgeEffects(sw, a, lKnow);

            sw.WriteLine(")");
            sw.WriteLine();
        }
/*
        private void WriteKnowledgeActions(StreamWriter sw)
        {
            foreach (Action a in Actions)
            {
                if (!a.HasConditionalEffects)
                    WriteKnowledgeAction(sw, a);
                else
                {
                    //BUGBUG - ff supports conditional effects
                    CompoundFormula cfObligatory = null;
                    List<Action> lSplit = a.SplitConditionalEffects(out cfObligatory);
                    List<Predicate> lKnow = new List<Predicate>();
                    cfObligatory.GetAllPredicates(lKnow);
                    if (a.Preconditions != null)
                        a.Preconditions.GetAllPredicates(lKnow);
                    foreach (Action aSplit in lSplit)
                        WriteConditionalSplitAction(sw, aSplit, lKnow);
                }
            }
        }
*/

        public List<Action> GetAllKnowledgeActions(Dictionary<string, List<Predicate>> dTags)
        {
            List<Action> lActions = new List<Action>();
            foreach (Action a in Actions)
            {
                if (a.Effects == null & a.Observe != null)
                {
                    Action aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    lActions.Add(aObserveTrue);
                    Action aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    lActions.Add(aObserveFalse);
                }

                else
                {
                    Action aKnowledge = a.AddTaggedConditions(dTags, m_lAlwaysKnown);
                    lActions.Add(aKnowledge);
                }
            }
            return lActions;
        }
        public List<Action> GetAllReasoningActions(Dictionary<string, List<Predicate>> dTags)
        {
            List<Action> lActions = new List<Action>();
            //get merges and tag refutation
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (!AlwaysKnown(pp))
                {
                    Action aMerge = GenerateMergeAction(pp, dTags);
                    lActions.Add(aMerge);
                    Action aRefute = GenerateRefutationAction(pp, true);
                    lActions.Add(aRefute);
                    aRefute = GenerateRefutationAction(pp, false);
                    lActions.Add(aRefute);
                }
            }
            return lActions;
        }

        private List<Action> GetKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Predicate> lAdditionalPredicates)
        {
            List<Action> lAllActions = new List<Action>();
            lAdditionalPredicates.Add(new GroundedPredicate("NotInAction"));

            foreach (Action a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    List<Action> lKnowWhether = a.TagObservationTranslationNoState(dTags, this);
                    lAllActions.AddRange(lKnowWhether);
                }
                else
                {
                    List<Action> lKnowWhether = a.TagCompilationNoState(dTags, this, lAdditionalPredicates);
                    lAllActions.AddRange(lKnowWhether);
                }
            }
            return lAllActions;
        }



        private List<Action> GetKnowledgeActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Predicate> lAdditionalPredicates)
        {
            List<Action> lAllActions = new List<Action>();
            lAdditionalPredicates.Add(new GroundedPredicate("NotInAction"));

            foreach (Action a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    Action aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    Action aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    lAllActions.Add(aObserveTrue);
                    lAllActions.Add(aObserveFalse);
                }
                else
                {
                    List<Action> lCompiled = a.KnowCompilationSplitConditions(dTags, m_lAlwaysKnown, lAdditionalPredicates);
                    lAllActions.AddRange(lCompiled);
                }
            }
            return lAllActions;
        }

        private void WriteKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            int cTranslatedActions = 0;
            foreach (Action a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    List<Action> lCompiled = a.TagObservationTranslationNoState(dTags, this);
                    foreach (Action aKnowWhether in lCompiled)
                        WriteConditionalAction(sw, aKnowWhether);
                }
                else
                {
                    List<Action> lCompiled = a.TagCompilationNoState(dTags, this, null);
                    foreach (Action aCompiled in lCompiled)
                    {
                        cTranslatedActions++;
                        WriteConditionalAction(sw, aCompiled);
                    }
                }
            }
        }


/*
        private void WriteKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            int  cTranslatedActions = 0;
            int cMaxTranslatedConditionalEffects = 0, cMaxOriginalConditionalEffects = 0;
            foreach (Action a in Actions)
            {
                //if (a.GetConditions().Count > cMaxOriginalConditionalEffects)
                //    cMaxOriginalConditionalEffects = a.GetConditions().Count;


                if (a.Effects == null && a.Observe != null)
                {
                    //Action aKnow = a.KnowObservationTranslation();
                    //WriteConditionalAction(sw, aKnow);
                    BUGBUG;
                    List<Action> lKnowWhether = a.KnowWhetherTagObservationTranslation(dTags, this);
                    foreach (Action aKnowWhether in lKnowWhether)
                        WriteConditionalAction(sw, aKnowWhether);
                }
                else
                {
                    //Action aKnow = a.KnowCompilation(dTags, this);
                    //WriteConditionalAction(sw, aKnow);
                    List<Action> lKnowWhether = a.KnowWhetherTagCompilation(dTags, this);
                    foreach (Action aKnowWhether in lKnowWhether)
                    {
                        cTranslatedActions++;
                        //if (aKnowWhether.GetConditions().Count > cMaxTranslatedConditionalEffects)
                        //    cMaxTranslatedConditionalEffects = aKnowWhether.GetConditions().Count;
                        WriteConditionalAction(sw, aKnowWhether);
                    }
                }
            }
            //Debug.WriteLine("Original: #Actions " + Actions.Count + ", Max conditions " + cMaxOriginalConditionalEffects);
            //Debug.WriteLine("Translated: #Actions " + cTranslatedActions + ", Max conditions " + cMaxTranslatedConditionalEffects);
        }
*/

        private void WriteKnowledgeActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    if (m_bReplaceNonDeterministicEffectsWithOptions)
                    {
                        Action aDeterministic = a.ReplaceNonDeterministicEffectsWithOptions(m_lAlwaysKnown);
                        Action aKnowledge = aDeterministic.AddTaggedConditions(dTags, m_lAlwaysKnown);
                        WriteConditionalAction(sw, aKnowledge);
                    }
                    else
                    {
                        List<Action> lKnowledgeActions = a.AddTaggedNonDeterministicConditions(dTags, m_lAlwaysKnown);
                        foreach (Action aKnowledge in lKnowledgeActions)
                            WriteConditionalAction(sw, aKnowledge);
                    }
                }
                 
                else if (a.Effects == null & a.Observe != null)
                {
                    Action aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    WriteConditionalAction(sw, aObserveTrue);
                    Action aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    WriteConditionalAction(sw, aObserveFalse);
                }
                    
                else
                {
                    Action aKnowledge = a.AddTaggedConditions(dTags, m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
                /* I can't split the effects like that becuase if KC/t -> KE/t even if C is not true
                if (a.HasConditionalEffects)
                {
                    List<Action> aSplitted = a.SplitTaggedConditions(dTags, m_lAlwaysKnown);
                    foreach (Action aKnowledge in aSplitted)
                        WriteConditionalAction(sw, aKnowledge);
                }
                else
                {
                    Action aKnowledge = a.AddKnowledge(m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
                 * */
            }
        }
        private void WriteReasoningActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            //write merges and tag refutation
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (!AlwaysKnown(pp))
                {
                    Action aMerge = GenerateMergeAction(pp, dTags);
                    WriteAction(sw, aMerge);
                    Action aRefute = GenerateRefutationAction(pp, true);
                    WriteAction(sw, aRefute);
                    aRefute = GenerateRefutationAction(pp, false);
                    WriteAction(sw, aRefute);
                    
                    //Action aAssert = GenerateAssertInvalid(pp, pCurrent.Goal);
                    //WriteAction(sw, aAssert);
                }
                /*
                List<Action> lRefutation = GenerateRefutationActions(pp, dTags);
                foreach (Action aRefute in lRefutation)
                    WriteAction(sw, aRefute);
                 * */
            }
        }

        private void WriteReasoningActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            List<List<string>[]> lAllPartitions = new List<List<string>[]>();
            Action.GetAllPartitions(new List<string>(dTags.Keys), lAllPartitions);
            //write merges and tag refutation
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (!(AlwaysKnown(pp) && AlwaysConstant(pp)) && pp.Name != OPTION_PREDICATE)
                {
                    Action aMerge = null;
                    //aMerge = GenerateKnowMergeAction(pp, this, dTags, true, false);
                    //WriteAction(sw, aMerge);
                    //aMerge = GenerateKnowMergeAction(pp, this, dTags, false, false);
                    //WriteAction(sw, aMerge);
                    /* this allows the planner to cheat somehow - not sure how but it does
                    aMerge = GenerateKnowUnMergeAction(pp, dTags, true);
                    WriteAction(sw, aMerge);
                    aMerge = GenerateKnowUnMergeAction(pp, dTags, false);
                    WriteAction(sw, aMerge);
                     * */
                    if (!AlwaysKnown(pp))
                    {
                        //aMerge = GenerateKnowMergeAction(pp, this, dTags, true, true);
                        //WriteAction(sw, aMerge);
                        //aMerge = GenerateKnowUnMergeAction(pp, dTags, true, false);
                        //WriteAction(sw, aMerge);
                        //aMerge = GenerateKnowUnMergeAction(pp, dTags, false, false);
                        //WriteAction(sw, aMerge);
                        //aMerge = GenerateKnowUnMergeAction(pp, dTags, true, true);
                        //WriteAction(sw, aMerge);
                    }


                    if (!AlwaysKnown(pp))
                    {
                        foreach (List<string>[] aPartition in lAllPartitions)
                        {
                            aMerge = GenerateTagMergeAction(pp, aPartition[0], aPartition[1], true);
                            WriteAction(sw, aMerge);
                            aMerge = GenerateTagMergeAction(pp, aPartition[0], aPartition[1], false);
                            WriteAction(sw, aMerge);
                        }
                    }
                    if(Observable(pp))
                    {
                        Action aRefute = GenerateTagRefutationGiven(pp, dTags);
                        WriteAction(sw, aRefute);
                    }
                }
            }
        }

        private bool Observable(ParametrizedPredicate pp)
        {
            foreach (Action a in Actions)
            {
                if (a.Observe != null)
                {
                    HashSet<Predicate> lObservables = a.Observe.GetAllPredicates();
                    foreach(Predicate p in lObservables)
                    {
                        if (p.Name == pp.Name)
                            return true;
                    }

                }
            }
            return false;
        }

        private Action GenerateTagMergeAction(ParametrizedPredicate pp, List<string> lIncludedTags, List<string> lExcludedTags, bool bValue)
        {
            string sName = "TagMerge-" + pp.Name;
            foreach (string sTag in lIncludedTags)
                sName += "-" + sTag;
            if (bValue == true)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");

            foreach (string sTag in lIncludedTags)
            {
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == VALUE)
                        p.Name = VALUE_PARAMETER;

                if (bValue == true)
                    cfAnd.AddOperand(ppKGivenT);
                else
                    cfAnd.AddOperand(ppKGivenT.Negate());

                if (sTag != lIncludedTags[0])
                {
                    ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
                    pKNotT.AddParameter(new Constant(TAG, sTag));
                    pKNotT.AddParameter(new Constant(TAG, lIncludedTags[0]));
                    cfAnd.AddOperand(pKNotT.Negate());
                }
            }
            foreach (string sTag in lExcludedTags)
            {
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == VALUE)
                        p.Name = VALUE_PARAMETER;
                ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
                pKNotT.AddParameter(new Constant(TAG, sTag));
                pKNotT.AddParameter(new Constant(TAG, lIncludedTags[0]));
                cfAnd.AddOperand(pKNotT);
            }
            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            foreach (string sTag in lIncludedTags)
            {
                Predicate ppK = pp.GenerateKnowGiven(sTag, true);
                cfAnd.AddOperand(ppK);
            }
            
            pa.SetEffects(cfAnd);
            return pa;
        }


        private Action GenerateTagMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue)
        {
            string sName = "TagMerge-" + pp.Name;
            if (bValue == true)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pTag = new Parameter(TAG, TAG_PARAMETER);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");

            foreach (string sTag in dTags.Keys)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == VALUE)
                        p.Name = VALUE_PARAMETER;

                ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
                pKNotT.AddParameter(new Constant(TAG, sTag));
                pKNotT.AddParameter(pTag);
                if (bValue == true)
                    cfOr.AddOperand(ppKGivenT);
                else
                    cfOr.AddOperand(ppKGivenT.Negate());
                cfOr.AddOperand(pKNotT);
                cfAnd.AddOperand(cfOr);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            Predicate ppK = pp.GenerateKnowGiven(TAG_PARAMETER, true);
            cfAnd.AddOperand(ppK);
            pa.SetEffects( cfAnd);
            return pa;
        }

        private Action GenerateTagRefutationGiven(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            ParametrizedAction pa = new ParametrizedAction("Refute-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pTag1 = new Parameter(TAG, TAG_PARAMETER + "1");
            pa.AddParameter(pTag1);
            Parameter pTag2 = new Parameter(TAG, TAG_PARAMETER + "2");
            pa.AddParameter(pTag2);
            CompoundFormula cfAnd = new CompoundFormula("and");

            cfAnd.AddOperand(pp.GenerateGiven(TAG_PARAMETER + "1"));
            cfAnd.AddOperand(pp.Negate().GenerateGiven(TAG_PARAMETER + "2"));
            cfAnd.AddOperand(pp.GenerateKnowGiven(TAG_PARAMETER + "1", true));
            cfAnd.AddOperand(pp.GenerateKnowGiven(TAG_PARAMETER + "2", true));

            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKnowNot1Given2 = new ParametrizedPredicate("KNot");
            ppKnowNot1Given2.AddParameter(pTag1);
            ppKnowNot1Given2.AddParameter(pTag2);
            cfAnd.AddOperand(ppKnowNot1Given2);
            ParametrizedPredicate ppKnowNot2Given1 = new ParametrizedPredicate("KNot");
            ppKnowNot2Given1.AddParameter(pTag2);
            ppKnowNot2Given1.AddParameter(pTag1);
            cfAnd.AddOperand(ppKnowNot2Given1);

            pa.SetEffects( cfAnd);
            return pa;
        }


        private Action GenerateMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            ParametrizedAction pa = new ParametrizedAction("Merge-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pValue = new Parameter(Domain.VALUE, VALUE_PARAMETER);
            pa.AddParameter(pValue);
            CompoundFormula cfAnd = new CompoundFormula("and");
            /*
            ParametrizedPredicate ppK = new ParametrizedPredicate("K" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppK.AddParameter(param);
             */
            KnowPredicate ppK = new KnowPredicate(pp);
            ppK.Parametrized = true;
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p

            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            foreach (string sTag in dTags.Keys)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
                GroundedPredicate pKNotT = new GroundedPredicate("KNot");
                pKNotT.AddConstant(new Constant(TAG, sTag));
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                ppKGivenT.AddParameter(pValue);
                cfOr.AddOperand(new PredicateFormula(ppKGivenT));
                cfOr.AddOperand(new PredicateFormula(pKNotT));
                cfAnd.AddOperand(cfOr);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.SetEffects( cfAnd);
            return pa;
        }

        private Action GenerateKnowMergeAction(ParametrizedPredicate pp, Domain d, Dictionary<string, List<Predicate>> dTags, bool bValue, bool bKnowWhether)
        {
            ParametrizedAction pa = null;
            string sName = "";
            if (bKnowWhether)
            {
                sName = "Merge-KW-" + pp.Name;
            }
            else
            {
                sName = "Merge-K-" + pp.Name;
                if (bValue == true)
                    sName += "-T";
                else
                    sName += "-F";
            }
            pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = null;
            if (bKnowWhether)
            {
                ppK = new KnowWhetherPredicate(pp);
            }
            else
            {
                ppK = new KnowPredicate(pp, bValue, false);
            }
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = null;
                if (bKnowWhether)
                    ppKGivenT = new ParametrizedPredicate("KWGiven" + pp.Name);
                else
                {
                    ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                }
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                if(!bKnowWhether && bValue == false)
                    cfAnd.AddOperand(ppKGivenT.Negate());
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            if (!bKnowWhether && !d.AlwaysKnown(pp))
                cfAnd.AddOperand(new KnowWhetherPredicate(pp));
            pa.SetEffects( cfAnd);
            return pa;
        }

        private Action GenerateKnowUnMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue, bool bKnowWhether)
        {
            ParametrizedAction pa = null;
            if (bKnowWhether)
                pa = new ParametrizedAction("UnMerge-KW-" + pp.Name);
            else
                pa = new ParametrizedAction("UnMerge-K-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = null;
            if (bKnowWhether)
            {
                ppK = new KnowWhetherPredicate(pp);
            }
            else
            {
                ppK = new KnowPredicate(pp, bValue, false);
            }
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = null;
                if (bKnowWhether)
                    ppKGivenT = new ParametrizedPredicate("KWGiven" + pp.Name);
                else
                    ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                if (!bKnowWhether && bValue == false)
                {
                    cfAnd.AddOperand(ppKGivenT.Negate());
                }
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.SetEffects( cfAnd);
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.Preconditions = cfAnd;
            return pa;
        }

        private Action GenerateKnowUnMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue)
        {
            string sName = "UnMerge-K-" + pp.Name;
            if (bValue)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);

            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = new KnowPredicate(pp, bValue, false);
            
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(TAG, sTag));
                if (bValue == false)
                {
                    cfAnd.AddOperand(ppKGivenT.Negate());
                }
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.SetEffects( cfAnd);
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.Preconditions = cfAnd;
            return pa;
        }

        private Action GenerateRefutationAction(ParametrizedPredicate pp, bool bValue)
        {
            string sName = "Refute";
            if (bValue)
                sName += "T";
            else
                sName += "F";
            sName += "-" + pp.Name;
            ParametrizedAction pa = new ParametrizedAction(sName);
            Parameter pTag = new Parameter(TAG, TAG_PARAMETER);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            if (bValue)
                ppKGivenT.AddParameter(new Constant(Domain.VALUE, Domain.TRUE_VALUE));
            else
                ppKGivenT.AddParameter(new Constant(Domain.VALUE, Domain.FALSE_VALUE));

            ParametrizedPredicate pKNotT = new ParametrizedPredicate("KNot");
            pKNotT.AddParameter(pTag);
            cfAnd.AddOperand(pKNotT.Negate());//add ~know not t - if we already know that t is false there is no point in running tag refutation

            if (SDRPlanner.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            /*
            ParametrizedPredicate ppK = new ParametrizedPredicate("K" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppK.AddParameter(param);
            */
            KnowPredicate ppK = new KnowPredicate(pp, !bValue, false);
            cfAnd.AddOperand(ppKGivenT);
            cfAnd.AddOperand(ppK);

            if (bValue)
                cfAnd.AddOperand(pp.Negate());
            else
                cfAnd.AddOperand(pp);

            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(new PredicateFormula(pKNotT));
            pa.SetEffects( cfAnd);
            return pa;
        }


        private Action GenerateAssertInvalid(ParametrizedPredicate pp, Formula fGoal)
        {
            string sName = "AssertInvalid";
            sName += "_" + pp.Name;
            ParametrizedAction pa = new ParametrizedAction(sName);
            Parameter pTag = new Parameter(TAG, TAG_PARAMETER);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            ppKGivenT.AddParameter(new Parameter(Domain.VALUE, Domain.TRUE_VALUE));
            cfAnd.AddOperand(ppKGivenT);

            ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            ppKGivenT.AddParameter(new Parameter(Domain.VALUE, Domain.FALSE_VALUE));
            cfAnd.AddOperand(ppKGivenT);

            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(fGoal);

            HashSet<Predicate> lAllGoal = fGoal.GetAllPredicates();
            foreach (Predicate p in lAllGoal)
            {
                if(!AlwaysKnown(p))
                    cfAnd.AddOperand(new KnowPredicate(p));
            } 

            pa.SetEffects( cfAnd);
            return pa;
        }


        private List<Action> GenerateRefutationActions(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            List<Action> lRefutations = new List<Action>();
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedAction pa = new ParametrizedAction("Refute-" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    pa.AddParameter(param);
                CompoundFormula cfAnd = new CompoundFormula("and");
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("K" + pp.Name + "_" + sTag);
                GroundedPredicate pKNotT = new GroundedPredicate("KNot");
                pKNotT.AddConstant(new Constant(TAG, sTag));
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                cfAnd.AddOperand(new PredicateFormula(ppKGivenT));
                cfAnd.AddOperand(pp.Negate());
                pa.Preconditions = cfAnd;
                cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(new PredicateFormula(pKNotT));
                pa.SetEffects(cfAnd);
                lRefutations.Add(pa);
            }
            return lRefutations;
        }

        private void WriteKnowledgeActions(StreamWriter sw)
        {
            foreach (Action a in Actions)
            {
                if (!a.HasConditionalEffects)
                    WriteKnowledgeAction(sw, a);
                else
                {
                    Action aKnowledge = a.AddKnowledgeConditions(m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
            }
        }

        private void RemoveConflictingConditionalEffectsFromAction(Action a)
        {
            CompoundFormula cfPreconditions = null;
            if (a.Preconditions == null)
            {
                cfPreconditions = new CompoundFormula("and");
                a.Preconditions = cfPreconditions;
            }
            else if (a.Preconditions is PredicateFormula)
            {
                cfPreconditions = new CompoundFormula("and");
                cfPreconditions.AddOperand(a.Preconditions);
                a.Preconditions = cfPreconditions;
            }
            else
            {
                cfPreconditions = (CompoundFormula)a.Preconditions;
            }
            cfPreconditions.AddOperand(new GroundedPredicate("axioms-applied"));

            CompoundFormula cfEffects = new CompoundFormula("and");
            cfEffects.AddOperand(new GroundedPredicate("axioms-applied").Negate());
            if (a.Effects is PredicateFormula)
            {
                cfEffects.AddOperand(a.Effects);
                a.SetEffects( cfEffects);
            }
            else
            {
                CompoundFormula cfOldEffects = (CompoundFormula)a.Effects;
                foreach (Formula f in cfOldEffects.Operands)
                {
                    if (f is PredicateFormula)
                        cfEffects.AddOperand(f);
                    else
                        cfEffects.AddOperand(((CompoundFormula)f).ReplaceNegativeEffectsInCondition());

                }
            }
            a.SetEffects( cfEffects);
        }

        private void WriteConditionalAction(StreamWriter sw, Action aKnowledge)
        {
            sw.WriteLine("(:action " + aKnowledge.Name);
            if (aKnowledge is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)aKnowledge;
                sw.Write(":parameters (");
                foreach (Parameter param in pa.Parameters)
                    sw.Write(" " + param.Name + " - " + param.Type);
                sw.WriteLine(")");
            }
            if (RemoveConflictingConditionalEffects)
            {
                RemoveConflictingConditionalEffectsFromAction(aKnowledge);
            }


            if (aKnowledge.Preconditions != null)
                sw.WriteLine(":precondition " + aKnowledge.Preconditions);
            sw.WriteLine(":effect " + aKnowledge.Effects.ToString().Replace("(when", "\n\t(when"));
            sw.WriteLine(")");
        }
        /* using KW predicates
        private void WriteTaggedPredicatesNoState(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                /*
                if (pp.Name != Domain.OPTION_PREDICATE)
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");
                }
                 * *
                if (AlwaysConstant(pp) && AlwaysKnown(pp))
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");
                }
                if (!AlwaysConstant(pp) || !AlwaysKnown(pp))
                {
                    /*
                    sw.Write("(KGiven" + pp.Name);//write know-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");
                     * *
                    sw.Write("(Given" + pp.Name);//write given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.WriteLine(")");
                }
                if (!AlwaysKnown(pp) && pp.Name != Domain.OPTION_PREDICATE)
                {
                    /*
                    sw.Write("(KW" + pp.Name);//write know-whether predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    *
                    //maybe we can further remove this for constant predicates? Not sure.
                    sw.Write("(KWGiven" + pp.Name);//write know-whether-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.WriteLine(")");
                }
            }

            sw.WriteLine("(KNot " + TAG_PARAMETER + "1 - " + TAG + " " + TAG_PARAMETER + "2 - " + TAG + ")");//for tag refutation

            for (int iTime = 0; iTime < TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }
*/

        private void WriteTaggedPredicatesNoState(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            if(lAdditinalPredicates == null)
                sw.WriteLine("(NotInAction)");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (AlwaysConstant(pp) && AlwaysKnown(pp))
                {
                    sw.Write("(" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }
                if (!AlwaysConstant(pp) || !AlwaysKnown(pp))
                {
                    sw.Write("(Given" + pp.Name);//write given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.WriteLine(")");
                    if (SDRPlanner.SplitConditionalEffects)
                    {
                        sw.Write("(Given" + pp.Name + "-Add");//write givenp-add predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.WriteLine(")");
                        sw.Write("(Given" + pp.Name + "-Remove");//write givenp-remove predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.WriteLine(")");
                    }
                }
            }

            sw.WriteLine("(KNot " + TAG_PARAMETER + "1 - " + TAG + " " + TAG_PARAMETER + "2 - " + TAG + ")");//for tag refutation

            for (int iTime = 0; iTime < TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }


        private void WriteTaggedPredicates(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");


                if (RemoveConflictingConditionalEffects)
                {
                    sw.Write("(Not-" + pp.Name);//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }

                if (SDRPlanner.SplitConditionalEffects)
                {
                    sw.Write("(" + pp.Name + "-Add");//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    sw.Write("(" + pp.Name + "-Remove");//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }

                if (!AlwaysKnown(pp))
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");

                    if (RemoveConflictingConditionalEffects)
                    {
                        sw.Write("(Not-K" + pp.Name);//write regular predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }

                    if (SDRPlanner.SplitConditionalEffects)
                    {
                        sw.Write("(K" + pp.Name + "-Add");//write know predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                        sw.Write("(K" + pp.Name + "-Remove");//write know predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }

                    sw.Write("(KGiven" + pp.Name);//write know-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                    sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                    sw.WriteLine(")");

                    if (RemoveConflictingConditionalEffects)
                    {
                        sw.Write("(Not-KGiven" + pp.Name);//write regular predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }

                    if (SDRPlanner.SplitConditionalEffects)
                    {
                        sw.Write("(KGiven" + pp.Name + "-Add");//write know-given predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                        sw.Write("(KGiven" + pp.Name + "-Remove");//write know-given predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + TAG_PARAMETER + " - " + TAG);
                        sw.Write(" " + VALUE_PARAMETER + " - " + VALUE);
                        sw.WriteLine(")");
                    }
                }
            }
            sw.WriteLine("(KNot " + TAG_PARAMETER + " - " + TAG + ")");//for tag refutation

            if (RemoveConflictingConditionalEffects)
            {
                sw.WriteLine("(axioms-applied)");
                HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
                foreach (GroundedPredicate gp in lGrounded)
                {
                    sw.Write("(axioms-applied-" + gp.Name);
                    foreach (Constant c in gp.Constants)
                        sw.Write("-" + c.Name);
                    sw.WriteLine(")");
                }

            }
            /*
            if (m_bUseOptions)
            {
                sw.WriteLine("(option ?x - " + OPTION + ")");
            }
            */
            for (int iTime = 0; iTime < TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }

        private void WriteKnowledgePredicates(StreamWriter sw)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
                sw.Write("(K" + pp.Name);//write know predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {
                sw.Write(" " + p.Key + " - " + TAG + " ;");
                foreach (Predicate pred in p.Value)
                {
                    sw.Write(" " + pred.ToString());
                }
                sw.WriteLine();
            }
            sw.WriteLine(" " + TRUE_VALUE + " - " + VALUE);
            sw.WriteLine(" " + FALSE_VALUE + " - " + VALUE);
            /*
            if (m_bUseOptions && HasNonDeterministicActions())
            {
                int cOptions = MaxNonDeterministicEffects();
                for( int i = 0 ; i < cOptions ; i++ )
                    sw.Write(" " + "opt" + i + " - " + OPTION);
                sw.WriteLine();
            }
             * */
            sw.WriteLine(")");
        }

        private void WriteTypes(StreamWriter sw, bool bUseTags)
        {
            sw.Write("(:types");
            foreach (string sType in Types)
            {
                if(!TypeHierarchy.ContainsKey(sType))
                    sw.Write(" " + sType);
            }
            if (bUseTags)
            {
                sw.Write(" " + TAG);
                sw.Write(" " + VALUE);
            }
 
            foreach (string sType in Types)
            {
                if (TypeHierarchy.ContainsKey(sType))
                    sw.Write("\n" + sType + " - " + TypeHierarchy[sType]);
            }
            /*
            if (m_bUseOptions && HasNonDeterministicActions())
            {
                sw.Write(" " + OPTION);
            }
             * */
            sw.WriteLine(")");
        }

        public bool HasNonDeterministicActions()
        {
            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                    return true;
            }
            return false;
        }

        public int MaxNonDeterministicEffects()
        {
            int cMaxOptions = 0;
            foreach (Action a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    if (a.Effects.GetMaxNonDeterministicOptions() > cMaxOptions)
                        cMaxOptions = a.Effects.GetMaxNonDeterministicOptions();
                }
            }
            return cMaxOptions;
        }

        private Action GetActionByName(string sActionName)
        {
            foreach (Action a in Actions)
            {
                if (a.Name.ToLower() == sActionName.ToLower())
                {
                    return a;
                }
                if (a.Name.ToLower().Replace("_", "-") == sActionName)
                    return a;
            }
            Action aBestMatch = null;
            foreach (Action a in Actions)
            {
                if (sActionName.StartsWith(a.Name.ToLower())) //assuming that this is a splitted conditional effect action. BUGBUG - need better solution for this
                {
                    if (aBestMatch == null || aBestMatch.Name.Length < a.Name.Length)
                        aBestMatch = a;
                }
                if (sActionName.StartsWith(a.Name.ToLower().Replace("_", "-"))) //assuming that this is a splitted conditional effect action. BUGBUG - need better solution for this
                {
                    if (aBestMatch == null || aBestMatch.Name.Length < a.Name.Length)
                        aBestMatch = a;
                }
            }
            return aBestMatch;
        }
        private Dictionary<string, Constant> GetBindings(ParametrizedAction pa, string[] asAction)
        {
            if (pa.Parameters.Count > asAction.Length - 1)//last parameter can be the tag of a KW action
                return null;
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            for (int iParameter = 0; iParameter < pa.Parameters.Count; iParameter++)
            {
                Constant c = GetConstant(pa.Parameters[iParameter].Type, asAction[iParameter + 1]);
                if (c == null)
                    return null;
                dBindings[pa.Parameters[iParameter].Name] = c;
            }
            return dBindings;
        }

        private Constant GetConstant(string sType, string sName)
        {
            foreach (Constant c in Constants)
            {
                if (c.Name == sName)
                {
                    if (ParentOf(sType, c.Type))
                        return c;

                }
            }
            return null;
        }
        public Action GroundActionByName(string[] asAction, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            string sActionName = asAction[0];
            Action a = GetActionByName(sActionName);
            if(!(a is ParametrizedAction))
                return a;
            ParametrizedAction pa = (ParametrizedAction)a;                       
            Dictionary<string, Constant> dBindings = GetBindings(pa, asAction);

            Formula fGroundedPreconditions = null;
            if(pa.Preconditions != null)
                fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
            if (pa.Preconditions == null || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
            {
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                    sName += "_" + dBindings[p.Name].Name;
                Action aGrounded = new Action(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                if (pa.Effects != null)
                    aGrounded.SetEffects( pa.Effects.Ground(dBindings));
                if (pa.Observe != null)
                    aGrounded.Observe = pa.Observe.Ground(dBindings);
                return aGrounded;
            }
            return null;
        }

        public Action GroundActionByName(string[] asAction)
        {
            string sActionName = asAction[0];
            Action a = GetActionByName(sActionName);
            if (!(a is ParametrizedAction))
                return a;
            ParametrizedAction pa = (ParametrizedAction)a;
            Dictionary<string, Constant> dBindings = GetBindings(pa, asAction);

            Formula fGroundedPreconditions = null;
            if (pa.Preconditions != null)
                fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
            else if (pa.Effects != null)
                pa.Effects.Ground(dBindings);
            else if (pa.Observe != null)
                pa.Observe.Ground(dBindings);
            string sName = pa.Name;
            foreach (Parameter p in pa.Parameters)
                sName += "_" + dBindings[p.Name].Name;
            Action aGrounded = new Action(sName);
            aGrounded.Preconditions = fGroundedPreconditions;
            if (pa.Effects != null)
                aGrounded.SetEffects( pa.Effects.Ground(dBindings));
            if (pa.Observe != null)
                aGrounded.Observe = pa.Observe.Ground(dBindings);
            return aGrounded;
        }

        public void GroundPredicate(ParametrizedPredicate pp, Dictionary<Parameter, Constant> dBindings, List<Argument> lRemaining, HashSet<GroundedPredicate> lGrounded)
        {
            if (lRemaining.Count == 0)
            {
                GroundedPredicate gp = new GroundedPredicate(pp.Name);
                foreach (Parameter p in pp.Parameters)
                    gp.AddConstant(dBindings[p]);
                lGrounded.Add(gp);
            }
            else
            {
                Argument a = lRemaining[0];
                List<Argument> lNewRemaining = new List<Argument>(lRemaining);
                lNewRemaining.RemoveAt(0);
                if (a is Parameter)
                {
                    Parameter p = (Parameter)a;
                    foreach (Constant c in Constants)
                    {
                        if (p.Type == "" || c.Type == p.Type)
                        {
                            dBindings[p] = c;
                            GroundPredicate(pp, dBindings, lNewRemaining, lGrounded);
                        }
                    }
                }
                else
                {
                    GroundPredicate(pp, dBindings, lNewRemaining, lGrounded);
                }
            }
        }

        public List<Action> GroundAllActions(List<Action> lActions, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            List<Action> lGrounded = new List<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }

            }
            foreach (Action a in lActions)
            {
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    lToBind = new List<Parameter>(pa.Parameters);
                    dBindings.Clear();
                    //GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                    GroundAction(pa, lConstants, lToBind, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                }
                else
                {
                    if (a.Preconditions == null || !bCheckConsistency || a.Preconditions.IsTrue(lPredicates, bContainsNegations))
                        lGrounded.Add(a);
                }
            }
            return lGrounded;
        }






        /*
        public List<Action> GroundAllActions(List<Action> lActions, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            List<Action> lGrounded = new List<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }

            }
            foreach (Action a in lActions)
            {
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    lToBind = new List<Parameter>(pa.Parameters);
                    dBindings.Clear();
                    //GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                    GroundAction(pa, lConstants, lToBind, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                }
                else
                {
                    if (a.Preconditions == null || !bCheckConsistency || a.Preconditions.IsTrue(lPredicates, bContainsNegations))
                        lGrounded.Add(a);
                }
            }
            return lGrounded;
        }
        */
        public List<Action> GroundAllActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            return GroundAllActions(Actions, lPredicates, bContainsNegations, true);
        }

        public List<Action> GroundAllActions()
        {
            //throw new NotImplementedException();
            return GroundAllActions(null);
        }

        private Domain m_dGrounded;
        private List<Action> m_lNoConstantActions;
        public void StartGrounding(Problem problem, HashSet<GroundedPredicate> lPublicFacts)
        {
            m_dGrounded = Clone();
            m_dGrounded.PublicPredicates = new HashSet<Predicate>();
            m_dGrounded.PrivatePredicates = new HashSet<Predicate>();
            m_dGrounded.Actions = new List<Action>();
            m_dGrounded.PublicActions = new HashSet<Action>();
            m_dGrounded.PrivateActions = new HashSet<Action>();
            mapActionNameToAction = new Dictionary<string, Action>();

            m_lNoConstantActions = GroundConstantPredicates(problem);
        }

        public void ContinueGrounding(Problem problem, HashSet<GroundedPredicate> lPublicFacts)
        {
            Dictionary<string, HashSet<GroundedPredicate>> dPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
            List<Action> lActions = GroundAllActions(problem, dPredicates, lPublicFacts);
            
            
            HashSet<string> lPrivatePredicateNames = new HashSet<string>();
            foreach (Predicate p in PrivatePredicates)
                lPrivatePredicateNames.Add(p.Name);
            foreach (KeyValuePair<string, HashSet<GroundedPredicate>> pair in dPredicates)
            {
                foreach (GroundedPredicate gp in pair.Value)
                    m_dGrounded.Predicates.Add(gp);
                if (lPrivatePredicateNames.Contains(pair.Key))
                {
                    foreach (GroundedPredicate gp in pair.Value)
                        m_dGrounded.PrivatePredicates.Add(gp);
                }
                else if (PrivateConstants.Count == 0)
                {
                    foreach (GroundedPredicate gp in pair.Value)
                    {
                        m_dGrounded.PublicPredicates.Add(gp);
                        lPublicFacts.Add(gp);
                    }
                }
                else
                {
                    foreach (GroundedPredicate gp in pair.Value)
                    {
                        bool bPrivatePredicate = false;
                        foreach (Constant c in gp.Constants)
                            if (PrivateConstants.Contains(c))
                                bPrivatePredicate = true;
                        if (bPrivatePredicate)
                            m_dGrounded.PrivatePredicates.Add(gp);
                        else
                        {
                            m_dGrounded.PublicPredicates.Add(gp);
                            lPublicFacts.Add(gp);
                        }
                    }
                }
            }
            foreach (Action a in lActions)
            {

                
                m_dGrounded.Actions.Add(a);
                if (a.Effects == null)
                    m_dGrounded.PublicActions.Add(a);
                else
                {
                    bool bPrivateAction = true;
                    HashSet<Predicate> lEffects = a.Effects.GetAllPredicates();
                    foreach (Predicate p in lEffects)
                    {
                        if (!(p is GroundedFunctionPredicate) && (m_dGrounded.PublicPredicates.Contains(p) || m_dGrounded.PublicPredicates.Contains(p.Negate())))
                            bPrivateAction = false;
                    }
                    if (bPrivateAction)
                        m_dGrounded.PrivateActions.Add(a);
                    else
                        m_dGrounded.PublicActions.Add(a);
                }
            }
        }
        public Domain FinishGrounding(int i)
        {
           
            m_dGrounded.mapActionNameToAction=new Dictionary<string,Action>();
            m_dGrounded.Actions = new List<Action>(m_dGrounded.PublicActions.ToList());
            m_dGrounded.Actions.AddRange(m_dGrounded.PrivateActions);
            m_dGrounded.Predicates = new HashSet<Predicate>(Predicates);
            HashSet<Action> del = new HashSet<Action>();
            foreach (Action act in m_dGrounded.Actions)
            {
                act.agent = "Agent: " + i.ToString();
                act.LoadPrecondition();
                if (m_dGrounded.mapActionNameToAction.ContainsKey(act.Name.ToLower()))
                {
                    del.Add(act);
                    continue;
                }
                m_dGrounded.mapActionNameToAction.Add(act.Name.ToLower(), act);
            }
            foreach (Action act in del)
            {
                //m_dGrounded.Actions.Remove(act);
            }
            return m_dGrounded;
        }

        public Domain Ground(Problem problem)
        {
            Domain dGrounded = Clone();
            dGrounded.PublicPredicates = new HashSet<Predicate>();
            dGrounded.PrivatePredicates = new HashSet<Predicate>();
            dGrounded.PublicActions = new HashSet<Action>();
            dGrounded.PrivateActions = new HashSet<Action>();
            HashSet<string> lPrivatePredicateNames = new HashSet<string>();
            foreach (Predicate p in PrivatePredicates)
                lPrivatePredicateNames.Add(p.Name);
            Dictionary<string, HashSet<GroundedPredicate>> dPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
            List<Action> lActions = GroundAllActions(problem, dPredicates);
            foreach (KeyValuePair<string, HashSet<GroundedPredicate>> pair in dPredicates)
            {
                foreach (GroundedPredicate gp in pair.Value)
                    dGrounded.Predicates.Add(gp);
                if (lPrivatePredicateNames.Contains(pair.Key))
                {
                    foreach (GroundedPredicate gp in pair.Value)
                        dGrounded.PrivatePredicates.Add(gp);
                }
                else if (PrivateConstants.Count == 0)
                {
                    foreach (GroundedPredicate gp in pair.Value)
                        dGrounded.PublicPredicates.Add(gp);
                }
                else
                {
                    foreach (GroundedPredicate gp in pair.Value)
                    {
                        bool bPrivatePredicate = false;
                        foreach (Constant c in gp.Constants)
                            if (PrivateConstants.Contains(c))
                                bPrivatePredicate = true;
                        if (bPrivatePredicate)
                            dGrounded.PrivatePredicates.Add(gp);
                        else
                            dGrounded.PublicPredicates.Add(gp);
                    }
                }
            }
            foreach (Action a in lActions)
            {
                dGrounded.Actions.Add(a);
                if (a.Effects == null)
                    dGrounded.PublicActions.Add(a);
                else
                {
                    bool bPrivateAction = false;
                    HashSet<Predicate> lEffects = a.Effects.GetAllPredicates();
                    foreach (Predicate p in lEffects)
                    {
                        if (dGrounded.PrivatePredicates.Contains(p))
                            bPrivateAction = true;
                    }
                    if (bPrivateAction)
                        dGrounded.PrivateActions.Add(a);
                    else
                        dGrounded.PublicActions.Add(a);
                }
            }
            return dGrounded;
        }
        public List<Action> GroundAllActions(Problem problem)
        {
            Dictionary<string, HashSet<GroundedPredicate>> dPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
            return GroundAllActions(problem, dPredicates);
        }


        private List<GroundedPredicate> GroundPredicate(ParametrizedPredicate pp, List<Parameter> lToBind)
        {
            List<GroundedPredicate> lAll = new List<GroundedPredicate>();
            Parameter p = lToBind.First();
            List<Parameter> lRemaining = new List<Parameter>(lToBind);
            lRemaining.Remove(p);
            foreach (Constant c in Constants)
            {
                if (ParentOf(p.Type, c.Type))
                {
                    Dictionary<string,Constant> dBindings = new Dictionary<string,Constant>();
                    dBindings.Add(p.Name, c);
                    Predicate pNew = pp.PartiallyGround(dBindings);
                    if (pNew is GroundedPredicate)
                    {
                        lAll.Add((GroundedPredicate)pNew);
                    }
                    else
                    {
                        List<GroundedPredicate> lRes = GroundPredicate((ParametrizedPredicate)pNew, lRemaining);
                        lAll.AddRange(lRes);

                    }
                }

            }
            return lAll;

        }

        public HashSet<GroundedPredicate> GroundAllPredicates()
        {
            HashSet<GroundedPredicate> lAll = new HashSet<GroundedPredicate>();
            foreach (Predicate p in Predicates)
            {
                if (p is GroundedPredicate)
                    lAll.Add((GroundedPredicate)p);
                else
                {
                    ParametrizedPredicate pp = (ParametrizedPredicate)p;
                    List<Parameter> lToBind = new List<Parameter>();
                    foreach (Argument a in pp.Parameters)
                        if (a is Parameter)
                            lToBind.Add((Parameter)a);
                    List<GroundedPredicate> lPredicates = GroundPredicate((ParametrizedPredicate)p, lToBind);
                    lAll.UnionWith(lPredicates);
                }

            }
            return lAll;
        }

        private List<Action> GroundAllActionsII(Problem problem, Dictionary<string, HashSet<GroundedPredicate>> dPredicates)
        {
            HashSet<GroundedPredicate> lPredicates = GroundAllPredicates();

            HashSet<Action> lAllGrounded = new HashSet<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();

            
            foreach (GroundedPredicate gp in lPredicates)
            {
                if (!gp.Negation)
                {
                    if (!dPredicates.ContainsKey(gp.Name))
                        dPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                    dPredicates[gp.Name].Add(gp);
                }
            }

            bool bNewPredciatesAdded = true;
            int cIterations = 0;
            while (bNewPredciatesAdded)
            {
                HashSet<Action> lGrounded = new HashSet<Action>();
                Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
                foreach (Action a in Actions)
                {
                    if (a is ParametrizedAction)
                    {
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();

                        bool bNoValidGrounding = false;
                        List<ParametrizedPredicate> lPreconditionPredicatesToBind = new List<ParametrizedPredicate>();
                        HashSet<Predicate> lAllPredicates = pa.Preconditions.GetAllPredicates();
                        foreach (Predicate p in lAllPredicates)
                        {
                            if (p is ParametrizedPredicate)
                            {
                                if (!dPredicates.ContainsKey(p.Name))
                                    bNoValidGrounding = true;
                                lPreconditionPredicatesToBind.Add((ParametrizedPredicate)p);
                            }
                        }
                        List<ParametrizedPredicate> lEffectPredicatesToBind = new List<ParametrizedPredicate>();
                        foreach(Predicate p in pa.Effects.GetAllPredicates())
                            if(p is ParametrizedPredicate)
                                lEffectPredicatesToBind.Add((ParametrizedPredicate)p);
                        if (!bNoValidGrounding)
                        {
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>();
                            GroundAction(pa, dPredicates, lToBind, dBindings, lPreconditionPredicatesToBind,lEffectPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);
                        }
                    }
                    else
                    {
                        
                        lGrounded.Add(a);
                    }
                }

                bNewPredciatesAdded = false;
                foreach (string sKey in dNewPredicates.Keys)
                {
                    if (!dPredicates.ContainsKey(sKey))
                        dPredicates[sKey] = new HashSet<GroundedPredicate>();
                    foreach (GroundedPredicate gp in dNewPredicates[sKey])
                    {
                        if (!dPredicates[sKey].Contains(gp))
                        {
                            dPredicates[sKey].Add(gp);
                            bNewPredciatesAdded = true;
                        }
                    }
                }

                foreach (Action a in lGrounded)
                {
                    if (!lAllGrounded.Contains(a))
                    {
                        a.LoadPrecondition();
                        lAllGrounded.Add(a);

                    }
                }
                cIterations++;
                //Console.WriteLine("....");

            }
            mapActionNameToAction = new Dictionary<string, Action>();

            groundedAction = lAllGrounded.ToList();
            foreach (Action a in groundedAction)
            {
                mapActionNameToAction.Add(a.Name.ToLower(), a);
            }
            return groundedAction;
           
        }


        //efficient grounding usign start state - problematic in MA setting - does not find all possible actions
        private List<Action> GroundConstantPredicates(Problem problem)
        {
            HashSet<Action> lAllGrounded = new HashSet<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            HashSet<GroundedPredicate> lPredicates = new HashSet<GroundedPredicate>();
            Dictionary<string, HashSet<GroundedPredicate>> dPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();


            foreach (Predicate p in problem.Known)
            {
                if (p is GroundedPredicate && AlwaysConstant(p))
                    lPredicates.Add((GroundedPredicate)p);
            }
            HashSet<Predicate> lHidden = new HashSet<Predicate>();
            foreach (CompoundFormula cf in problem.Hidden)
            {
                cf.GetAllPredicates(lHidden);
            }
            foreach (GroundedPredicate gp in lHidden)
                lPredicates.Add(gp);
            foreach (GroundedPredicate gp in lPredicates)
            {
                if (!gp.Negation)
                {
                    if (!dPredicates.ContainsKey(gp.Name))
                        dPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                    dPredicates[gp.Name].Add(gp);
                }
            }

            HashSet<Action> lGrounded = new HashSet<Action>();

            foreach (Action a in Actions)
            {
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    lToBind = new List<Parameter>(pa.Parameters);
                    dBindings.Clear();

                    bool bNoValidGrounding = false;
                    List<ParametrizedPredicate> lPreconditionPredicatesToBind = new List<ParametrizedPredicate>();
                    HashSet<Predicate> lAllPredicates = pa.Preconditions.GetAllPredicates();
                    foreach (Predicate p in lAllPredicates)
                    {
                        if (p is ParametrizedPredicate && AlwaysConstant(p))
                        {
                            if (!p.Negation)//not adding negations to the list of predicates to bind, because the state maintains only positives.
                            {
                                if (!dPredicates.ContainsKey(p.Name))
                                    bNoValidGrounding = true;
                                lPreconditionPredicatesToBind.Add((ParametrizedPredicate)p);
                            }
                        }
                    }
                    //cannot have constants in effects
                    List<ParametrizedPredicate> lEffectPredicatesToBind = new List<ParametrizedPredicate>();
                    if (!bNoValidGrounding)
                    {
                        Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>();
                        GroundConstants(pa, dPredicates, lToBind, dBindings, lPreconditionPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded);
                    }
                }
                else
                {

                    lGrounded.Add(a);
                }
            }

            return new List<Action>(lGrounded);

        }
       
 

        //efficient grounding usign start state - problematic in MA setting - does not find all possible actions
        private List<Action> GroundAllActions(Problem problem, Dictionary<string, HashSet<GroundedPredicate>> dPredicates, HashSet<GroundedPredicate> lPublicFacts)
        {
            HashSet<Action> lAllGrounded = new HashSet<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            HashSet<GroundedPredicate> lPredicates = new HashSet<GroundedPredicate>(lPublicFacts);

            foreach (Predicate p in problem.Known)
            {
                if (p is GroundedPredicate)
                    lPredicates.Add((GroundedPredicate)p);
            }
            HashSet<Predicate> lHidden = new HashSet<Predicate>();
            foreach (CompoundFormula cf in problem.Hidden)
            {
                cf.GetAllPredicates(lHidden);
            }
            foreach (GroundedPredicate gp in lHidden)
                lPredicates.Add(gp);
            foreach (GroundedPredicate gp in lPredicates)
            {
                if (!gp.Negation)
                {
                    if (!dPredicates.ContainsKey(gp.Name))
                        dPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                    dPredicates[gp.Name].Add(gp);
                }
            }

            bool bNewPredciatesAdded = true;
            int cIterations = 0;
            while (bNewPredciatesAdded)
            {
                HashSet<Action> lGrounded = new HashSet<Action>();
                Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
                foreach (Action a in m_lNoConstantActions)
                {
                    if (a is ParametrizedAction)
                    {
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();

                        bool bNoValidGrounding = false;
                        List<ParametrizedPredicate> lPreconditionPredicatesToBind = new List<ParametrizedPredicate>();
                        HashSet<Predicate> lAllPredicates = pa.Preconditions.GetAllPredicates();
                        foreach (Predicate p in lAllPredicates)
                        {
                            if (p is ParametrizedPredicate)
                            {
                                if (!p.Negation)//not adding negations to the list of predicates to bind, because the state maintains only positives.
                                {
                                    if (!dPredicates.ContainsKey(p.Name))
                                        bNoValidGrounding = true;
                                    lPreconditionPredicatesToBind.Add((ParametrizedPredicate)p);
                                }
                            }
                            else if (p is GroundedPredicate)
                            {
                                if (!p.Negation)
                                {
                                    if (!dPredicates.ContainsKey(p.Name) || !dPredicates[p.Name].Contains((GroundedPredicate)p))
                                        bNoValidGrounding = true;
                                }
                            }
                        }
                        List<ParametrizedPredicate> lEffectPredicatesToBind = new List<ParametrizedPredicate>();
                        foreach (Predicate p in pa.Effects.GetAllPredicates())
                            if (p is ParametrizedPredicate)
                                lEffectPredicatesToBind.Add((ParametrizedPredicate)p);
                        if (!bNoValidGrounding)
                        {
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>();
                            GroundAction(pa, dPredicates, lToBind, dBindings, lPreconditionPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);
                        }
                    }
                    else
                    {

                        lGrounded.Add(a);
                    }
                }

                bNewPredciatesAdded = false;
                foreach (string sKey in dNewPredicates.Keys)
                {
                    if (!dPredicates.ContainsKey(sKey))
                        dPredicates[sKey] = new HashSet<GroundedPredicate>();
                    foreach (GroundedPredicate gp in dNewPredicates[sKey])
                    {
                        if (!dPredicates[sKey].Contains(gp))
                        {
                            dPredicates[sKey].Add(gp);
                            bNewPredciatesAdded = true;
                        }
                    }
                }

                foreach (Action a in lGrounded)
                {
                    if (!lAllGrounded.Contains(a))
                    {
                        //a.LoadPrecondition(); what is that?
                        lAllGrounded.Add(a);

                    }
                }
                cIterations++;
                //Console.WriteLine("....");

            }
            mapActionNameToAction = new Dictionary<string, Action>();

            groundedAction = lAllGrounded.ToList();
            foreach (Action a in groundedAction)
            {
                mapActionNameToAction.Add(a.Name.ToLower(), a);
            }
            return groundedAction;

        }
       
        
        //efficient grounding usign start state - problematic in MA setting - does not find all possible actions
        private List<Action> GroundAllActions(Problem problem, Dictionary<string, HashSet<GroundedPredicate>> dPredicates)
        {
            if (groundedAction != null) return groundedAction;
            // Console.WriteLine("Started grounding");
            HashSet<Action> lAllGrounded = new HashSet<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();

            foreach (Predicate p in problem.Known)
            {
                if (p is GroundedPredicate)
                    lPredicates.Add(p);
            }
            foreach (CompoundFormula cf in problem.Hidden)
            {
                cf.GetAllPredicates(lPredicates);
            }
            foreach (GroundedPredicate gp in lPredicates)
            {
                if (!gp.Negation)
                {
                    if (!dPredicates.ContainsKey(gp.Name))
                        dPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                    dPredicates[gp.Name].Add(gp);
                }
            }



            bool bNewPredciatesAdded = true;
            int cIterations = 0;
            while (bNewPredciatesAdded)
            {
                HashSet<Action> lGrounded = new HashSet<Action>();
                Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
                foreach (Action a in Actions)
                {
                    if (a is ParametrizedAction)
                    {
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();

                        bool bNoValidGrounding = false;
                        List<ParametrizedPredicate> lPreconditionPredicatesToBind = new List<ParametrizedPredicate>();
                        HashSet<Predicate> lAllPredicates = pa.Preconditions.GetAllPredicates();
                        foreach (Predicate p in lAllPredicates)
                        {
                            if (p is ParametrizedPredicate)
                            {
                                if (!dPredicates.ContainsKey(p.Name))
                                    bNoValidGrounding = true;
                                lPreconditionPredicatesToBind.Add((ParametrizedPredicate)p);
                            }
                        }
                        List<ParametrizedPredicate> lEffectPredicatesToBind = new List<ParametrizedPredicate>();
                        foreach (Predicate p in pa.Effects.GetAllPredicates())
                            if (p is ParametrizedPredicate)
                                lEffectPredicatesToBind.Add((ParametrizedPredicate)p);
                        if (!bNoValidGrounding)
                        {
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>();
                            GroundAction(pa, dPredicates, lToBind, dBindings, lPreconditionPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);
                        }
                    }
                    else
                    {

                        lGrounded.Add(a);
                    }
                }

                bNewPredciatesAdded = false;
                foreach (string sKey in dNewPredicates.Keys)
                {
                    if (!dPredicates.ContainsKey(sKey))
                        dPredicates[sKey] = new HashSet<GroundedPredicate>();
                    foreach (GroundedPredicate gp in dNewPredicates[sKey])
                    {
                        if (!dPredicates[sKey].Contains(gp))
                        {
                            dPredicates[sKey].Add(gp);
                            bNewPredciatesAdded = true;
                        }
                    }
                }

                foreach (Action a in lGrounded)
                {
                    if (!lAllGrounded.Contains(a))
                    {
                        a.LoadPrecondition();
                        lAllGrounded.Add(a);

                    }
                }
                cIterations++;
                //Console.WriteLine("....");

            }
           

            groundedAction = lAllGrounded.ToList();
            foreach (Action a in groundedAction)
            {
                mapActionNameToAction.Add(a.Name.ToLower(), a);
            }
            return groundedAction;

        }
        public List<Action> GroundAllObservationActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<Action> lGrounded = new List<Action>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            HashSet<Predicate> lToBind = null;
            //List<Constant> lConstants = new List<Constant>();
            /* can't use these because the observations do not appear in the preconditions
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }
            }
             * */
            foreach (Action a in Actions)
            {
                if (a.Observe != null)
                {
                    if (a is ParametrizedAction)
                    {
                        /*
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();
                        GroundAction(pa, Constants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, true);
                         */
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new HashSet<Predicate>();
                        if (pa.Preconditions != null)
                            pa.Preconditions.GetAllPredicates(lToBind);
                        dBindings.Clear();
                        GroundAction(pa, Constants, new List<Predicate>(lToBind), dBindings, lGrounded, lPredicates, bContainsNegations, true);

                    }
                    else
                        lGrounded.Add(a);
                }
            }
            List<Action> lFilteredKnown = new List<Action>();
            foreach (Action a in lGrounded)
            {
                PredicateFormula pf = (PredicateFormula)a.Observe;
                if (!lPredicates.Contains(pf.Predicate) &&
                    !lPredicates.Contains(pf.Predicate.Negate()))
                    lFilteredKnown.Add(a);
            }
            return lFilteredKnown;
        }

        private void GroundAction(ParametrizedAction pa, HashSet<Constant> lConstants,
            List<Parameter> lToBind, Dictionary<string, Constant> dBindings,
            List<Action> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            Formula fGroundedPreconditions = null;
            if (lToBind.Count > 0)
            {
                Parameter p = lToBind.First();
                lToBind.Remove(p);
                foreach (Constant c in lConstants)
                {
                    if (c.Type == p.Type)
                    {
                        dBindings[p.Name] = c;

                        if (pa.Preconditions != null)
                            fGroundedPreconditions = pa.Preconditions.PartiallyGround(dBindings);
                        if (pa.Preconditions == null || !bCheckConsistency || !fGroundedPreconditions.IsFalse(lPredicates, bContainsNegations))
                            GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                        else
                            Debug.Assert(false);
                    }
                }
                dBindings.Remove(p.Name);
                lToBind.Add(p);
            }
            else
            {
                if(pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                if (pa.Preconditions == null || !bCheckConsistency || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
                {
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += "_" + dBindings[p.Name].Name;
                    Action aGrounded = new Action(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    if (pa.Effects != null)
                        aGrounded.SetEffects( pa.Effects.Ground(dBindings));
                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    if((pa.Preconditions == null || !aGrounded.Preconditions.IsFalse(new List<Predicate>()) )&&
                        (aGrounded.Effects == null || !aGrounded.Effects.IsFalse(new List<Predicate>())))
                        lGrounded.Add(aGrounded);
                }
            }
        }

        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Parameter> lToBind,
            List<Action> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            Formula fGroundedPreconditions = null;
            List<Predicate> lPre = new List<Predicate>();
            if (pa.Preconditions != null)
                lPre = new List<Predicate>(pa.Preconditions.GetAllPredicates());
            List<Dictionary<string, Constant>> lBindings = FindValidBindings(lToBind, lPre, lPredicates, bContainsNegations);
            foreach (var dBindings in lBindings) 
            {
                if (pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                if (pa.Preconditions == null || !bCheckConsistency || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
                {
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += "_" + dBindings[p.Name].Name;
                    Action aGrounded = new Action(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    if (pa.Effects != null)
                        aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    if ((pa.Preconditions == null || !aGrounded.Preconditions.IsFalse(new List<Predicate>())) &&
                        (aGrounded.Effects == null || !aGrounded.Effects.IsFalse(new List<Predicate>())))
                        lGrounded.Add(aGrounded);
                }
            }
        }



        private void FindValidBindings(List<Parameter> lToBind, List<Dictionary<string, Constant>> lBindings, Dictionary<string, Constant> dBinding, bool bContainsNegations)
        {
            if (lToBind.Count == 0 )
            {
                lBindings.Add(dBinding);
                return;
            }

            Parameter pFirst = lToBind[0];
            List<Parameter> lNewToBind = new List<Parameter>(lToBind);
            lNewToBind.RemoveAt(0);
            foreach (Constant c in Constants)
            {
                if (c.Type == pFirst.Type)
                {
                    Dictionary<string, Constant> dNewBinding = new Dictionary<string, Constant>(dBinding);
                    dNewBinding[pFirst.Name] = c;
                    FindValidBindings(lNewToBind, lBindings, dNewBinding, bContainsNegations);
                }
            }
        }



        private void FindValidBindings(List<Parameter> lToBind, List<Dictionary<string, Constant>> lBindings, Dictionary<string, Constant> dBinding,
            List<Predicate> lPreconditions, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            if (lToBind.Count == 0 || lPreconditions.Count == 0)
            {
                if (lToBind.Count != 0)
                    FindValidBindings(lToBind, lBindings, dBinding, bContainsNegations);
                else
                    lBindings.Add(dBinding);
                return;
            }



            Predicate p = lPreconditions[0];
            List<Predicate> lReducedPreconditions = new List<Predicate>();
            for (int i = 1; i < lPreconditions.Count; i++)
                lReducedPreconditions.Add(lPreconditions[i]);

            if (p != null && p is ParametrizedPredicate && ((ParametrizedPredicate)p).Parameters.Count() > 0)
            {
                ParametrizedPredicate pCurrent = (ParametrizedPredicate)p;
                if (pCurrent.Negation && !bContainsNegations)
                    throw new NotImplementedException();


                List<GroundedPredicate> lMatches = new List<GroundedPredicate>();
                foreach (GroundedPredicate pGrounded in lPredicates)
                {
                    if (pCurrent.Name == pGrounded.Name && pCurrent.Negation == pGrounded.Negation)
                        lMatches.Add(pGrounded);
                }

                foreach (GroundedPredicate gpMatch in lMatches)
                {
                    Dictionary<string, Constant> dNewBinding = pCurrent.Match(gpMatch, dBinding);
                    if (dNewBinding != null)
                    {
                        foreach (var v in dBinding)
                            dNewBinding[v.Key] = v.Value;
                        List<Parameter> lNewToBind = new List<Parameter>();
                        foreach (Parameter param in lToBind)
                        {
                            bool bExists = false;
                            foreach (string s in dNewBinding.Keys)
                                if (param.Name == s)
                                    bExists = true;
                            if (!bExists)
                                lNewToBind.Add(param);
                        }
                        FindValidBindings(lNewToBind, lBindings, dNewBinding, lReducedPreconditions, lPredicates, bContainsNegations);
                    }

                }

            }
            else
            {
                FindValidBindings(lToBind, lBindings, dBinding, lReducedPreconditions, lPredicates, bContainsNegations);

            }


        }


        private List<Dictionary<string, Constant>> FindValidBindings(List<Parameter> lToBind, List<Predicate> lPreconditions, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<Dictionary<string, Constant>> lBindings = new List<Dictionary<string, Constant>>();
            Dictionary<string, Constant> dBinding = new Dictionary<string, Constant>();

            Predicate pAt = null;
            for (int i = 0; i < lPreconditions.Count; i++)
            {
                if (lPreconditions[i].Name == "at")
                {
                    pAt = lPreconditions[i];
                    lPreconditions[i] = lPreconditions[0];
                    lPreconditions[0] = pAt;
                    break;
                }
            }
 
            FindValidBindings(lToBind, lBindings, dBinding, lPreconditions, lPredicates, bContainsNegations);
            return lBindings;
        }



        private void GroundAction(ParametrizedAction pa, HashSet<Constant> lConstants,
            List<Predicate> lToBind, Dictionary<string, Constant> dBindings,
            List<Action> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            if (lToBind.Count > 0)
            {
                ParametrizedPredicate p = (ParametrizedPredicate)lToBind.First();
                lToBind.Remove(p);
                foreach (GroundedPredicate pExists in lPredicates)
                {
                    Dictionary<string, Constant> dNewBindings = p.Match(pExists, dBindings);
                    if (dNewBindings != null)
                    {
                        foreach (KeyValuePair<string, Constant> pair in dNewBindings)
                        {
                            dBindings[pair.Key] = pair.Value;
                        }
                        GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                        foreach (KeyValuePair<string, Constant> pair in dNewBindings)
                        {
                            dBindings.Remove(pair.Key);
                        }
                    }
                }
                lToBind.Add(p);
            }
            else
            {
                List<Parameter> lUnboundedParameters = new List<Parameter>();
                foreach (Parameter p in pa.Parameters)
                {
                    if (!dBindings.ContainsKey(p.Name))
                        lUnboundedParameters.Add(p);
                }
                GroundAction(pa, lConstants, lUnboundedParameters, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
            }
                
        }
        private void GroundAction(ParametrizedAction pa, Dictionary<string, HashSet<GroundedPredicate>> dPredicates,
            List<Parameter> lToBind, Dictionary<string, Constant> dBindings,
            List<ParametrizedPredicate> lPreconditionPredicatesToBind, List<ParametrizedPredicate> lEffectPredicatesToBind,
            Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings,
            HashSet<Action> lGrounded, Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates)
        {
            if (lPreconditionPredicatesToBind.Count > 0)
            {
                ParametrizedPredicate ppCurrent = lPreconditionPredicatesToBind.First();
                GroundedPredicate gpGrounded = ppCurrent.Ground(dBindings);

                if (gpGrounded == null)
                {
                    HashSet<GroundedPredicate> lCandidates = dPredicates[ppCurrent.Name];
                    foreach (GroundedPredicate gpCandidate in lCandidates)
                    {
                        Dictionary<string, Constant> dNewBindings = gpCandidate.Bind(ppCurrent, this);
                        if (ConsistentBindings(dBindings, dNewBindings))
                        {
                            foreach (KeyValuePair<string, Constant> p in dBindings)
                                dNewBindings[p.Key] = p.Value;
                            List<ParametrizedPredicate> lNewPredicatesToBind = new List<ParametrizedPredicate>(lPreconditionPredicatesToBind);
                            lNewPredicatesToBind.Remove(ppCurrent);
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dNewPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>(dPredicateBindings);
                            dNewPredicateBindings[ppCurrent] = gpCandidate;

                            GroundAction(pa, dPredicates, lToBind, dNewBindings, lNewPredicatesToBind, lEffectPredicatesToBind, dNewPredicateBindings, lGrounded, dNewPredicates);
                        }
                    }
                }
                else
                {
                    if (dPredicates[ppCurrent.Name].Contains(gpGrounded))
                    {
                        List<ParametrizedPredicate> lNewPredicatesToBind = new List<ParametrizedPredicate>(lPreconditionPredicatesToBind);
                        lNewPredicatesToBind.Remove(ppCurrent);
                        GroundAction(pa, dPredicates, lToBind, dBindings, lNewPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);
                    }
                }
            }
            else if (lEffectPredicatesToBind.Count > 0)
            {
                ParametrizedPredicate ppCurrent = lEffectPredicatesToBind.First();
                GroundedPredicate gpGrounded = ppCurrent.Ground(dBindings);

                if (gpGrounded == null)
                {
                    ParametrizedPredicate pPartial = (ParametrizedPredicate)ppCurrent.PartiallyGround(dBindings);
                    foreach (Argument a in pPartial.Parameters)
                    {
                        if (a is Parameter)
                        {
                            Parameter p = (Parameter)a;
                            foreach (Constant c in Constants)
                            {
                                if (ParentOf(p.Type, c.Type) && !dBindings.Values.Contains(c))
                                {
                                    Dictionary<string, Constant> dNewBindings = new Dictionary<string, Constant>(dBindings);
                                    dNewBindings[p.Name] = c;

                                    GroundAction(pa, dPredicates, lToBind, dNewBindings, lPreconditionPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);

                                }
                            }
                            break;//rest of arguments taken care in the recursion

                        }
                    }
                }
                else
                {
                    List<ParametrizedPredicate> lNewPredicatesToBind = new List<ParametrizedPredicate>(lEffectPredicatesToBind);
                    lNewPredicatesToBind.Remove(ppCurrent);
                    GroundAction(pa, dPredicates, lToBind, dBindings, lPreconditionPredicatesToBind, lNewPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);
                }


            }
            else if (lToBind.Count != dBindings.Count)//some parameters do not appear in any predicate but we still must ground them
            {
                Parameter p = null;
                foreach (Parameter pTag in lToBind)
                    if (!dBindings.ContainsKey(pTag.Name))
                        p = pTag;
                foreach (Constant c in Constants)
                {
                    if (ParentOf(p.Type, c.Type) && !dBindings.Values.Contains(c))
                    {
                        Dictionary<string, Constant> dNewBindings = new Dictionary<string, Constant>(dBindings);
                        dNewBindings[p.Name] = c;

                        GroundAction(pa, dPredicates, lToBind, dNewBindings, lPreconditionPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates);

                    }
                }
            }
            else
            {
                Formula fGroundedPreconditions = null;
                if (pa.Preconditions != null)
                {
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                }

                string sName = pa.Name;
                List<Parameter> lOriginalParams = pa.Parameters;
                if (pa.GroundedFrom != null)
                {
                    lOriginalParams = pa.GroundedFrom.Parameters;
                    sName = pa.GroundedFrom.Name;
                }
                if (pa.Bindings != null)
                {
                    foreach (KeyValuePair<string, Constant> p in pa.Bindings)
                        dBindings[p.Key] = p.Value;
                }

                string sOutputName = "(" + sName;
                foreach (Parameter p in lOriginalParams)
                {
                    sName += "_" + dBindings[p.Name].Name;
                    sOutputName += " " + dBindings[p.Name].Name;
                }
                sOutputName += ")";
                MapGroundedActionNamesToOutputNames[sName] = sOutputName;

                Action aGrounded = new Action(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                bool bInvalidEffects = false;
                if (pa.Effects != null)
                {
                    aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                    foreach (GroundedPredicate gp in aGrounded.Effects.GetAllPredicates())
                    {
                        if (gp.Name == Domain.FALSE_PREDICATE)
                            bInvalidEffects = true;
                        if (!gp.Negation)
                        {
                            if (!dNewPredicates.ContainsKey(gp.Name))
                                dNewPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                            dNewPredicates[gp.Name].Add(gp);
                        }
                    }
                }
                if (!bInvalidEffects)
                {

                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    lGrounded.Add(aGrounded);
                }

            }
        }

        private void GroundConstants(ParametrizedAction pa, Dictionary<string, HashSet<GroundedPredicate>> dPredicates,
            List<Parameter> lToBind, Dictionary<string, Constant> dBindings,
            List<ParametrizedPredicate> lPreconditionPredicatesToBind, List<ParametrizedPredicate> lEffectPredicatesToBind,
            Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings,
            HashSet<Action> lGrounded)
        {
            if (lPreconditionPredicatesToBind.Count > 0)
            {
                ParametrizedPredicate ppCurrent = lPreconditionPredicatesToBind.First();
                GroundedPredicate gpGrounded = ppCurrent.Ground(dBindings);

                if (gpGrounded == null)
                {
                    HashSet<GroundedPredicate> lCandidates = dPredicates[ppCurrent.Name];
                    foreach (GroundedPredicate gpCandidate in lCandidates)
                    {
                        Dictionary<string, Constant> dNewBindings = gpCandidate.Bind(ppCurrent, this);
                        if (ConsistentBindings(dBindings, dNewBindings))
                        {
                            foreach (KeyValuePair<string, Constant> p in dBindings)
                                dNewBindings[p.Key] = p.Value;
                            List<ParametrizedPredicate> lNewPredicatesToBind = new List<ParametrizedPredicate>(lPreconditionPredicatesToBind);
                            lNewPredicatesToBind.Remove(ppCurrent);
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dNewPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>(dPredicateBindings);
                            dNewPredicateBindings[ppCurrent] = gpCandidate;

                            GroundConstants(pa, dPredicates, lToBind, dNewBindings, lNewPredicatesToBind, lEffectPredicatesToBind, dNewPredicateBindings, lGrounded);
                        }
                    }
                }
                else
                {
                    if (dPredicates[ppCurrent.Name].Contains(gpGrounded))
                    {
                        List<ParametrizedPredicate> lNewPredicatesToBind = new List<ParametrizedPredicate>(lPreconditionPredicatesToBind);
                        lNewPredicatesToBind.Remove(ppCurrent);
                        GroundConstants(pa, dPredicates, lToBind, dBindings, lNewPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded);
                    }
                }
            }
            else if (lEffectPredicatesToBind.Count > 0)
            {
                ParametrizedPredicate ppCurrent = lEffectPredicatesToBind.First();
                GroundedPredicate gpGrounded = ppCurrent.Ground(dBindings);

                if (gpGrounded == null)
                {
                    ParametrizedPredicate pPartial = (ParametrizedPredicate)ppCurrent.PartiallyGround(dBindings);
                    foreach (Argument a in pPartial.Parameters)
                    {
                        if (a is Parameter)
                        {
                            Parameter p = (Parameter)a;
                            foreach (Constant c in Constants)
                            {
                                if (ParentOf(p.Type, c.Type) && !dBindings.Values.Contains(c))
                                {
                                    Dictionary<string, Constant> dNewBindings = new Dictionary<string, Constant>(dBindings);
                                    dNewBindings[p.Name] = c;

                                    GroundConstants(pa, dPredicates, lToBind, dNewBindings, lPreconditionPredicatesToBind, lEffectPredicatesToBind, dPredicateBindings, lGrounded);
                                    
                                }
                            }
                            break;//rest of arguments taken care in the recursion

                        }
                    }
                }
                else
                {
                    List<ParametrizedPredicate> lNewPredicatesToBind = new List<ParametrizedPredicate>(lEffectPredicatesToBind);
                    lNewPredicatesToBind.Remove(ppCurrent);
                    GroundConstants(pa, dPredicates, lToBind, dBindings, lPreconditionPredicatesToBind, lNewPredicatesToBind, dPredicateBindings, lGrounded);
                }
            }
            else
            {
                Formula fGroundedPreconditions = null;
                if (pa.Preconditions != null)
                {
                    fGroundedPreconditions = pa.Preconditions.PartiallyGround(dBindings);
                }
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                {
                    string sParam = p.Name;
                    if (dBindings.ContainsKey(sParam))
                        sParam = dBindings[sParam].Name;
                    sName += "_" + sParam;
                }

                ParametrizedAction aPartiallyGrounded = new ParametrizedAction(sName);
                foreach (Parameter param in pa.Parameters)
                    if (!dBindings.ContainsKey(param.Name))
                        aPartiallyGrounded.Parameters.Add(param);
                aPartiallyGrounded.Preconditions = fGroundedPreconditions;
                bool bInvalidEffects = false;
                if (pa.Effects != null)
                {
                    aPartiallyGrounded.SetEffects(pa.Effects.PartiallyGround(dBindings));
                    HashSet<Predicate> lEffectPeedicates = aPartiallyGrounded.Effects.GetAllPredicates();
                    foreach (Predicate gp in lEffectPeedicates)
                    {
                        if (gp.Name == Domain.FALSE_PREDICATE)
                            bInvalidEffects = true;
                    }
                }
                if (!bInvalidEffects)
                {

                    if (pa.Observe != null)
                        aPartiallyGrounded.Observe = pa.Observe.Ground(dBindings);

                    aPartiallyGrounded.GroundedFrom = pa;
                    aPartiallyGrounded.Bindings = new Dictionary<string, Constant>(dBindings);

                    lGrounded.Add(aPartiallyGrounded);
                }

            }
        }

       /* private bool ConsistentBindings(Dictionary<string, Constant> d1, Dictionary<string, Constant> d2)
        {
            if (d2 == null)
                return false;
            Dictionary<string, string> dObjToParam = new Dictionary<string, string>();
            foreach (KeyValuePair<string, Constant> p in d1)
            {
                if (dObjToParam.ContainsKey(p.Value.Name))
                {
                    if (dObjToParam[p.Value.Name] != p.Key)
                        return false;
                }
                else
                    dObjToParam[p.Value.Name] = p.Key;
            }
            foreach (KeyValuePair<string, Constant> p in d2)
            {
                if (dObjToParam.ContainsKey(p.Value.Name))
                {
                    if (dObjToParam[p.Value.Name] != p.Key)
                        return false;
                }
                else
                    dObjToParam[p.Value.Name] = p.Key;
            }
            foreach (string sKey in d1.Keys)
            {
                if (d2.ContainsKey(sKey))
                {
                    if (!d1[sKey].Equals(d2[sKey]))
                        return false;
                }
            }
            return true;
        }*/
        private bool ConsistentBindings(Dictionary<string, Constant> d1, Dictionary<string, Constant> d2)
        {
            if (d2 == null)
                return false;
            // this code does not allow an object to be mapped to two different parameters. However, in Rover this is needed.
            /*
            Dictionary<string, string> dObjToParam = new Dictionary<string, string>();
            foreach (KeyValuePair<string, Constant> p in d1)
            {
                if (dObjToParam.ContainsKey(p.Value.Name))
                {
                    if (dObjToParam[p.Value.Name] != p.Key)
                        return false;
                }
                else
                    dObjToParam[p.Value.Name] = p.Key;
            }
            foreach (KeyValuePair<string, Constant> p in d2)
            {
                if (dObjToParam.ContainsKey(p.Value.Name))
                {
                    if (dObjToParam[p.Value.Name] != p.Key)
                        return false;
                }
                else
                    dObjToParam[p.Value.Name] = p.Key;
            }
             */
            foreach (string sKey in d1.Keys)
            {
                if (d2.ContainsKey(sKey))
                {
                    if (!d1[sKey].Equals(d2[sKey]))
                        return false;
                }
            }
            return true;
        }


        private void GroundAction(ParametrizedAction pa,
            List<Parameter> lToBind, Dictionary<string, Constant> dBindings,
            List<Action> lGrounded, Problem problem)
        {
            if (lToBind.Count > 0)
            {
                Parameter p = lToBind.Last();
                lToBind.Remove(p);
                foreach (Constant c in Constants)
                {
                    if (c.Type == p.Type)
                    {
                        dBindings[p.Name] = c;
                        GroundAction(pa, lToBind, dBindings, lGrounded, problem);
                    }
                }
                dBindings.Remove(p.Name);
                lToBind.Add(p);
            }
            else
            {
                Formula fGroundedPreconditions = null;
                if (pa.Preconditions != null)
                {
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                    if (problem != null && !CheckValidConstantPreconditions(fGroundedPreconditions, problem))
                    {
                        return;
                    }
                }
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                    sName += " " + dBindings[p.Name].Name;
                Action aGrounded = new Action(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                if (pa.Effects != null)
                    aGrounded.SetEffects( pa.Effects.Ground(dBindings));
                if (pa.Observe != null)
                    aGrounded.Observe = pa.Observe.Ground(dBindings);
                lGrounded.Add(aGrounded);

            }
        }

        private bool CheckValidConstantPreconditions(Formula fGroundedPreconditions, Problem problem)
        {
            if (fGroundedPreconditions is CompoundFormula)
            {
                foreach (Formula fSub in ((CompoundFormula)fGroundedPreconditions).Operands)
                {
                    if (!CheckValidConstantPreconditions(fSub, problem))
                        return false;
                }
                return true;
            }
            else
            {
                PredicateFormula pf = (PredicateFormula)fGroundedPreconditions;
                if (m_lAlwaysConstant.Contains(pf.Predicate.Name) && m_lAlwaysKnown.Contains(pf.Predicate.Name))
                {
                    if (!pf.IsTrue(problem.Known))
                        return false;
                }
                return true;
            }
        }




        public bool AlwaysKnown(Predicate p)
        {
            return m_lAlwaysKnown.Contains(p.Name);
        }

        public bool Observable(Predicate p)
        {
            return m_lObservable.Contains(p.Name);
        }

        public bool AlwaysConstant(Predicate p)
        {
            return m_lAlwaysConstant.Contains(p.Name);
        }

        public void AddHidden(CompoundFormula cf)
        {
            HashSet<Predicate> lUnknown = new HashSet<Predicate>();
            cf.GetAllPredicates(lUnknown);
            foreach (Predicate p in lUnknown)
                m_lAlwaysKnown.Remove(p.Name);
        }

        public void ComputeAlwaysKnown()
        {
            bool bChanged = true;
            while (bChanged)
            {
                bChanged = false;
                foreach (Action a in Actions)
                {
                    if (a.HasConditionalEffects)
                    {
                        foreach (CompoundFormula cfCondition in a.GetConditions())
                        {
                            HashSet<Predicate> lIfPredicates = new HashSet<Predicate>();
                            cfCondition.Operands[0].GetAllPredicates(lIfPredicates);
                            bool bAllKnown = true;
                            foreach (Predicate p in lIfPredicates)
                            {
                                if (!m_lAlwaysKnown.Contains(p.Name))
                                    bAllKnown = false;
                            }
                            if (!bAllKnown)
                            {
                                HashSet<Predicate> lThenPredicates = new HashSet<Predicate>();
                                cfCondition.Operands[1].GetAllPredicates(lThenPredicates);
                                foreach (Predicate p in lThenPredicates)
                                {
                                    if (m_lAlwaysKnown.Contains(p.Name))
                                    {
                                        bChanged = true;
                                        m_lAlwaysKnown.Remove(p.Name);
                                    }
                                }
                            }
                        }
                    }
                    if (a.Observe != null)
                    {
                        HashSet<Predicate> lPredicates = a.Observe.GetAllPredicates();
                        foreach (Predicate p in lPredicates)
                        {
                            if (m_lAlwaysKnown.Contains(p.Name))
                            {
                                m_lAlwaysKnown.Remove(p.Name);
                            }
                        }
                    }
                }
            }
        }


        private void WritePredicates(StreamWriter sw)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
           
            sw.WriteLine(")");
        }
       
        private void WriteKReplannerActions(StreamWriter sw)
        {
            foreach (Action a in Actions)
            {
                if (a.Observe == null)
                    WriteAction(sw, a);
                else
                    WriteSensor(sw, a);
            }
        }

        public void WriteKReplannerDomain(string sFileName)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain " + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw);
            sw.WriteLine();
            WriteKReplannerActions(sw);
            sw.WriteLine(")");
            sw.Close();
        }

        public void AddFunction(string sFunctionName)
        {
            Functions.Add(sFunctionName);
        }

        public bool IsFunctionExpression(string s)
        {
            s = s.ToLower();
            return s == "increase" || s == "decrease" || s == "=";
        }

        public CompoundFormula GetOptionsStatement()
        {
            CompoundFormula cfOneof = new CompoundFormula("oneof");
            int cOptions = Math.Max(MAX_OPTIONS, MaxNonDeterministicEffects());
            for (int iOption = 0; iOption < cOptions; iOption++)
            {
                GroundedPredicate gpCurrentOption = new GroundedPredicate(Domain.OPTION_PREDICATE);
                gpCurrentOption.AddConstant(new Constant(OPTION, "opt" + iOption));
                cfOneof.AddOperand(gpCurrentOption);
            }
            return cfOneof;

        }

        public bool IsObservationAction(string sActionName)
        {
            Action a = GetActionByName(sActionName);
            return a.Observe != null;
        }

        public MemoryStream WriteSimpleDomain(string sFileName)
        {
            MemoryStream msDomain = new MemoryStream();
            StreamWriter sw = new StreamWriter(msDomain);
            sw.WriteLine("(define (domain K" + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw);
            sw.WriteLine();
            WriteActions(sw, false);
            sw.WriteLine(")");
            sw.Flush();

            
                msDomain.Position = 0;
                StreamReader sr = new StreamReader(msDomain);
                StreamWriter swFile = new StreamWriter(sFileName);
                swFile.Write(sr.ReadToEnd());
                swFile.Close();
            
            return msDomain;

        }

        private void WriteActions(StreamWriter sw, bool bWriteObservationActions)
        {
            foreach (Action a in Actions)
            {
                if (bWriteObservationActions || a.Observe == null)
                    WriteAction(sw, a);
            }
        }

        public bool CompareTo(Domain d)
        {
            foreach (Action a in Actions)
            {
                bool bFound = false;
                foreach (Action aOther in d.Actions)
                {
                    if (a.Name == aOther.Name)
                    {
                        bFound = true;
                        if (!a.CompareTo(aOther))
                            return false;
                        break;
                    }
                }
                if (!bFound)
                    return false;
            }
            return true;
        }

        static bool CompareDomains(string sDomain1, string sDomain2)
        {
            Parser p = new Parser();
            Domain d1 = p.ParseDomain(sDomain1);
            Domain d2 = p.ParseDomain(sDomain2);
            return d1.CompareTo(d2);
        }

        public void RemoveUniversalQuantifiers(List<Predicate> lConstantPredicates)
        {
            List<Action> lFiltered = new List<Action>();
            foreach (Action a in Actions)
            {
                Action aFiltered = a.RemoveUniversalQuantifiers(Constants, lConstantPredicates, this);
                if (aFiltered != null)
                    lFiltered.Add(aFiltered);
                //a.SimplifyConditions();
            }
            Actions = lFiltered;
        }
        public Dictionary<Predicate, HashSet<Predicate>> IdentifyInvariants(List<Action> lActions)
        {
            Dictionary<Predicate, HashSet<Predicate>> dCandidateMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, HashSet<Predicate>> dMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, HashSet<Predicate>> dNotMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            foreach (Action a in lActions)
            {
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                HashSet<Predicate> lEffects = a.GetMandatoryEffects();
                foreach (Predicate p in lEffects)
                {
                    if (p.Negation == false)
                    {
                        foreach (Predicate pTag in lEffects)
                        {
                            if (!pTag.Equals(p) && pTag.Negation == false)
                            {
                                if (!dNotMutex.ContainsKey(p))
                                    dNotMutex[p] = new HashSet<Predicate>();
                                dNotMutex[p].Add(pTag);
                                if (!dNotMutex.ContainsKey(pTag))
                                    dNotMutex[pTag] = new HashSet<Predicate>();
                                dNotMutex[p].Add(p);
                            }
                        }
                    }
                }
                foreach (Predicate p in lPreconditions)
                {
                    Predicate pNegate = p.Negate();
                    if (lEffects.Contains(pNegate))
                    {
                        HashSet<Predicate> lCandidates = new HashSet<Predicate>();
                        foreach (Predicate pTag in lEffects)
                        {
                            //if (pTag.Name == p.Name && pTag.Negation == p.Negation && !pTag.Equals(p))
                            if (p.Similarity(pTag) > 0)
                            {
                                lCandidates.Add(pTag);
                                //if (p.ToString() == "(in-stack B2 S0)" || pTag.ToString() == "(clear B0 S0)")
                                //    Console.Write("*");

                            }
                        }
                        if (!dCandidateMutex.ContainsKey(p))
                            dCandidateMutex[p] = lCandidates;
                        else
                            dCandidateMutex[p].UnionWith(lCandidates);
                    }

                }

            }
            foreach (Action a in lActions)
            {
                List<Predicate> lEffects = new List<Predicate>(a.GetMandatoryEffects());
                for (int i = 0; i < lEffects.Count; i++)
                {
                    for (int j = i + 1; j < lEffects.Count; j++)
                    {
                        if (dCandidateMutex.ContainsKey(lEffects[i]))
                            dCandidateMutex[lEffects[i]].Remove(lEffects[j]);
                        if (dCandidateMutex.ContainsKey(lEffects[j]))
                            dCandidateMutex[lEffects[j]].Remove(lEffects[i]);
                    }
                }

            }
            foreach (Predicate p in dCandidateMutex.Keys)
            {
                dMutex[p] = new HashSet<Predicate>();
                foreach (Predicate pTag in dCandidateMutex[p])
                {
                    if (dCandidateMutex.ContainsKey(pTag))
                    {
                        if (dCandidateMutex[pTag].Contains(p))
                            dMutex[p].Add(pTag);
                    }
                    else
                    {
                        //pTag does not appear in the candidate list, which means that it is not an effect of any action
                        dMutex[p].Add(pTag);
                        if (!dMutex.ContainsKey(pTag))
                            dMutex[pTag] = new HashSet<Predicate>();
                        dMutex[pTag].Add(p);
                    }
                }

            }
            List<HashSet<Predicate>> lMutexClosure = new List<HashSet<Predicate>>();
            foreach (Predicate p in dMutex.Keys)
            {
                foreach (Predicate pMutex in dMutex[p])
                {
                    HashSet<Predicate> hsMutex = new HashSet<Predicate>();
                    hsMutex.Add(p);
                    hsMutex.Add(pMutex); 
                    Dictionary<Argument, HashSet<Predicate>> dInvariants = FindInvariantGroups(p, hsMutex);

                    foreach (KeyValuePair<Argument, HashSet<Predicate>> pair in dInvariants)
                    {
                        if (pair.Value.Count > 1)
                        {
                            HashSet<Predicate> hsClosure = new HashSet<Predicate>(pair.Value);
                            IdentifyMutexClosure(p, pair.Key, pMutex, dMutex, dNotMutex, hsClosure);
                            //                            if (p.Name == "in-stack" || pMutex.Name == "in-stack")
                            //                                Console.Write("*");
                            lMutexClosure.Add(hsClosure);
                        }
                    }
                }
            }
            /*
            foreach (Predicate p in dMutex.Keys)
            {
                HashSet<Predicate> hsMutex = dMutex[p];
                Dictionary<Argument, HashSet<Predicate>> dInvariants = FindInvariantGroups(p, hsMutex);

                foreach (KeyValuePair<Argument, HashSet<Predicate>> pair in dInvariants)
                {
                    HashSet<Predicate> hsClosure = new HashSet<Predicate>(pair.Value);
                    hsClosure.Add(p);
                    foreach (Predicate pTag in pair.Value)
                    {
                        IdentifyMutexClosure(p, pair.Key, pTag, dMutex, hsClosure);
                    }
                    lMutexClosure.Add(hsClosure);
                }
            }
            */
            Dictionary<Predicate, HashSet<Predicate>> dMutexClosure = new Dictionary<Predicate, HashSet<Predicate>>();
            foreach (HashSet<Predicate> hsClosure in lMutexClosure)
            {
                List<Predicate> lClosure = new List<Predicate>(hsClosure);
                for (int i = 0; i < lClosure.Count; i++)
                {
                    if (!dMutexClosure.ContainsKey(lClosure[i]))
                        dMutexClosure[lClosure[i]] = new HashSet<Predicate>();
                    for (int j = i + 1; j < hsClosure.Count; j++)
                    {
                        if (!dMutexClosure.ContainsKey(lClosure[j]))
                            dMutexClosure[lClosure[j]] = new HashSet<Predicate>();
                        dMutexClosure[lClosure[i]].Add(lClosure[j]);
                        dMutexClosure[lClosure[j]].Add(lClosure[i]);
                    }
                }
            }

            return dMutexClosure;
        }
        public Dictionary<Predicate, HashSet<Predicate>> IdentifyStrongInvariants(List<Action> lActions)
        {
            Dictionary<Predicate, HashSet<Predicate>> dCandidateMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, HashSet<Predicate>> dMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, HashSet<Predicate>> dNotMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            foreach (Action a in lActions)
            {
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                HashSet<Predicate> lEffects = a.GetMandatoryEffects();
                foreach (Predicate p in lEffects)
                {
                    if (p.Negation == false)
                    {
                        foreach (Predicate pTag in lEffects)
                        {
                            if (!pTag.Equals(p) && pTag.Negation == false)
                            {
                                if (!dNotMutex.ContainsKey(p))
                                    dNotMutex[p] = new HashSet<Predicate>();
                                dNotMutex[p].Add(pTag);
                                if (!dNotMutex.ContainsKey(pTag))
                                    dNotMutex[pTag] = new HashSet<Predicate>();
                                dNotMutex[p].Add(p);
                            }
                        }
                    }
                }
                foreach (Predicate p in lPreconditions)
                {
                    Predicate pNegate = p.Negate();
                    if (lEffects.Contains(pNegate))
                    {
                        HashSet<Predicate> lCandidates = new HashSet<Predicate>();
                        foreach (Predicate pTag in lEffects)
                        {
                            //if (pTag.Name == p.Name && pTag.Negation == p.Negation && !pTag.Equals(p))
                            if (p.Similarity(pTag) > 0)
                            {
                                lCandidates.Add(pTag);
                                //if (p.ToString() == "(in-stack B2 S0)" || pTag.ToString() == "(clear B0 S0)")
                                //    Console.Write("*");

                            }
                        }
                        if (!dCandidateMutex.ContainsKey(p))
                            dCandidateMutex[p] = lCandidates;
                        else
                            dCandidateMutex[p].UnionWith(lCandidates);
                    }

                }

            }
            foreach (Action a in lActions)
            {
                List<Predicate> lEffects = new List<Predicate>(a.GetMandatoryEffects());
                for (int i = 0; i < lEffects.Count; i++)
                {
                    for (int j = i + 1; j < lEffects.Count; j++)
                    {
                        if (dCandidateMutex.ContainsKey(lEffects[i]))
                            dCandidateMutex[lEffects[i]].Remove(lEffects[j]);
                        if (dCandidateMutex.ContainsKey(lEffects[j]))
                            dCandidateMutex[lEffects[j]].Remove(lEffects[i]);
                    }
                }

            }
            foreach (Predicate p in dCandidateMutex.Keys)
            {
                dMutex[p] = new HashSet<Predicate>();
                foreach (Predicate pTag in dCandidateMutex[p])
                {
                    if (dCandidateMutex.ContainsKey(pTag))
                    {
                        if (dCandidateMutex[pTag].Contains(p))
                            dMutex[p].Add(pTag);
                    }
                }

            }
            List<HashSet<Predicate>> lMutexClosure = new List<HashSet<Predicate>>();
            foreach (Predicate p in dMutex.Keys)
            {
                foreach (Predicate pMutex in dMutex[p])
                {
                    HashSet<Predicate> hsMutex = new HashSet<Predicate>();
                    hsMutex.Add(p);
                    hsMutex.Add(pMutex);
                    Dictionary<Argument, HashSet<Predicate>> dInvariants = FindInvariantGroups(p, hsMutex);

                    foreach (KeyValuePair<Argument, HashSet<Predicate>> pair in dInvariants)
                    {
                        if (pair.Value.Count > 1)
                        {
                            HashSet<Predicate> hsClosure = new HashSet<Predicate>(pair.Value);
                            IdentifyMutexClosureStrong(p, pair.Key, pMutex, dMutex, dNotMutex, hsClosure);
                            //                            if (p.Name == "in-stack" || pMutex.Name == "in-stack")
                            //                                Console.Write("*");
                            lMutexClosure.Add(hsClosure);
                        }
                    }
                }
            }
            /*
            foreach (Predicate p in dMutex.Keys)
            {
                HashSet<Predicate> hsMutex = dMutex[p];
                Dictionary<Argument, HashSet<Predicate>> dInvariants = FindInvariantGroups(p, hsMutex);

                foreach (KeyValuePair<Argument, HashSet<Predicate>> pair in dInvariants)
                {
                    HashSet<Predicate> hsClosure = new HashSet<Predicate>(pair.Value);
                    hsClosure.Add(p);
                    foreach (Predicate pTag in pair.Value)
                    {
                        IdentifyMutexClosure(p, pair.Key, pTag, dMutex, hsClosure);
                    }
                    lMutexClosure.Add(hsClosure);
                }
            }
            */
            Dictionary<Predicate, HashSet<Predicate>> dMutexClosure = new Dictionary<Predicate, HashSet<Predicate>>();
            foreach (HashSet<Predicate> hsClosure in lMutexClosure)
            {
                List<Predicate> lClosure = new List<Predicate>(hsClosure);
                for (int i = 0; i < lClosure.Count; i++)
                {
                    if (!dMutexClosure.ContainsKey(lClosure[i]))
                        dMutexClosure[lClosure[i]] = new HashSet<Predicate>();
                    for (int j = i + 1; j < hsClosure.Count; j++)
                    {
                        if (!dMutexClosure.ContainsKey(lClosure[j]))
                            dMutexClosure[lClosure[j]] = new HashSet<Predicate>();
                        dMutexClosure[lClosure[i]].Add(lClosure[j]);
                        dMutexClosure[lClosure[j]].Add(lClosure[i]);
                    }
                }
            }

            return dMutexClosure;
        }
        public class Pair<T>
        {
            public T T1 { get; private set; }
            public T T2 { get; private set; }
            private int m_iHash;
            public Pair(T t1, T t2)
            {
                T1 = t1;
                T2 = t2;
                m_iHash = 0;
            }
            public override bool Equals(object obj)
            {
                if (obj is Pair<T>)
                {
                    Pair<T> p = (Pair<T>)obj;
                    return T1.Equals(p.T1) && T2.Equals(p.T2) || T1.Equals(p.T2) && T2.Equals(p.T1);
                }
                return false;
            }
            public override int GetHashCode()
            {
                if (m_iHash == 0)
                    m_iHash = T1.GetHashCode() + T2.GetHashCode();
                return m_iHash;
            }
        }

        public Dictionary<Predicate, HashSet<Predicate>> IdentifyInvariantsGraphplan(List<Action> lActions)
        {

            HashSet<Pair<Action>> hsActionMutex = new HashSet<Pair<Action>>();
            HashSet<Pair<Predicate>> hsPropositionMutex = new HashSet<Pair<Predicate>>();
            Dictionary<Predicate, HashSet<Action>> dMapEffectsToActions = new Dictionary<Predicate, HashSet<Action>>();
            for (int iAction = 0; iAction < lActions.Count; iAction++)
            {
                Action a = lActions[iAction];
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                HashSet<Predicate> lEffects = a.GetMandatoryEffects();
                for (int iOtherAction = iAction + 1; iOtherAction < lActions.Count; iOtherAction++)
                {
                    Action aOther = lActions[iOtherAction];
                    HashSet<Predicate> lOtherPreconditions = aOther.Preconditions.GetAllPredicates();
                    HashSet<Predicate> lOtherEffects = aOther.GetMandatoryEffects();
                    bool bMutex = false;
                    foreach (Predicate p in lPreconditions)
                    {
                        Predicate pNegate = p.Negate();
                        if (lOtherPreconditions.Contains(pNegate))
                        {
                            bMutex = true;
                            break;
                        }
                    }
                    if (!bMutex)
                    {
                        foreach (Predicate p in lEffects)
                        {
                            Predicate pNegate = p.Negate();
                            if (lOtherPreconditions.Contains(pNegate) || lOtherEffects.Contains(pNegate))
                            {
                                bMutex = true;
                                break;
                            }
                        }
                    }
                    if (!bMutex)
                    {
                        foreach (Predicate p in lOtherEffects)
                        {
                            Predicate pNegate = p.Negate();
                            if (lPreconditions.Contains(pNegate))
                            {
                                bMutex = true;
                                break;
                            }
                        }
                    }
                    if (bMutex)
                        hsActionMutex.Add(new Pair<Action>(a, aOther));
                }
            }
            return null;
        }

        private HashSet<Argument> FindInvariants(Predicate p, HashSet<Predicate> hsMutex)
        {
            HashSet<Argument> hsInvariants = new HashSet<Argument>();
            if (p is GroundedPredicate)
            {
                GroundedPredicate gpGrounded = (GroundedPredicate)p;
                for (int i = 0; i < gpGrounded.Constants.Count; i++)
                {
                    Constant c = gpGrounded.Constants[i];
                    bool bInAll = true;
                    foreach (GroundedPredicate gp in hsMutex)
                    {
                        if (!gp.Constants[i].Equals(c))
                        {
                            bInAll = false;
                            break;
                        }
                    }
                    if (bInAll)
                        hsInvariants.Add(c);
                }
            }
            return hsInvariants;
        }

        private Dictionary<Argument, HashSet<Predicate>> FindInvariantGroups(Predicate p, HashSet<Predicate> hsMutex)
        {
            Dictionary<Argument, HashSet<Predicate>> dInvariantGroups = new Dictionary<Argument, HashSet<Predicate>>();
            if (p is GroundedPredicate)
            {
                GroundedPredicate gpGrounded = (GroundedPredicate)p;
                for (int i = 0; i < gpGrounded.Constants.Count; i++)
                {
                    HashSet<Predicate> hsInvariants = new HashSet<Predicate>();
                    Constant c = gpGrounded.Constants[i];
                    foreach (GroundedPredicate gp in hsMutex)
                    {
                        if (gp.Name == p.Name)
                        {
                            if (gp.Constants[i].Equals(c))
                            {
                                hsInvariants.Add(gp);
                            }
                        }
                        else
                        {
                            if (gp.Constants.Contains(c))
                            {
                                hsInvariants.Add(gp);
                            }

                        }
                    }
                    if (hsInvariants.Count > 0)
                        dInvariantGroups[c] = hsInvariants;
                }
            }
            return dInvariantGroups;
        }

        private void IdentifyMutexClosureStrong(Predicate pOrg, Argument aInvariant, Predicate pCurrent, Dictionary<Predicate, HashSet<Predicate>> dMutex, Dictionary<Predicate, HashSet<Predicate>> dNotMutex, HashSet<Predicate> hsClosure)
        {
            HashSet<Predicate> hsCandidates = dMutex[pCurrent];
            foreach (Predicate p in hsCandidates)
            {
                if (!hsClosure.Contains(p))
                {
                    if (pOrg.SameInvariant(p, aInvariant))
                    {
                        // transitive colsure only if not specified as impossible - too strong, identifies things that are not mutex. Example - in elevators does not allow two passengers to be together in the same elevator
                        bool bValid = true;
                        foreach (Predicate pTag in hsClosure)
                        {
                            if (dNotMutex.ContainsKey(p))
                            {
                                if (dNotMutex[p].Contains(pTag))
                                    bValid = false;
                            }
                        }
                        /*this is too weak - example in elevators does not see that a passenger cannot be in two floors together
                        bool bValid = true;
                        foreach (Predicate pTag in hsClosure)
                        {
                            if (dMutex.ContainsKey(p))
                            {
                                if (!dMutex[p].Contains(pTag))
                                    bValid = false;
                            }
                        }
                        */
                        if (bValid)
                        {
                            hsClosure.Add(p);
                            IdentifyMutexClosureStrong(pOrg, aInvariant, p, dMutex, dNotMutex, hsClosure);
                        }
                    }

                }
            }

        }
        private void IdentifyMutexClosure(Predicate pOrg, Argument aInvariant, Predicate pCurrent, Dictionary<Predicate, HashSet<Predicate>> dMutex, Dictionary<Predicate, HashSet<Predicate>> dNotMutex, HashSet<Predicate> hsClosure)
        {
            HashSet<Predicate> hsCandidates = dMutex[pCurrent];
            foreach (Predicate p in hsCandidates)
            {
                if (!hsClosure.Contains(p))
                {
                    if (pOrg.SameInvariant(p, aInvariant))
                    {
                        /* transitive colusre only if not specified as impossible - too strong, identifies things that are not mutex. Example - in elevators
                        bool bValid = true;
                        foreach (Predicate pTag in hsClosure)
                        {
                            if (dNotMutex.ContainsKey(p))
                            {
                                if (dNotMutex[p].Contains(pTag))
                                    bValid = false;
                            }
                        }
                         * */
                        bool bValid = true;
                        foreach (Predicate pTag in hsClosure)
                        {
                            if (dMutex.ContainsKey(p))
                            {
                                if (!dMutex[p].Contains(pTag))
                                    bValid = false;
                            }
                        }

                        if (bValid)
                        {
                            hsClosure.Add(p);
                            IdentifyMutexClosure(pOrg, aInvariant, p, dMutex, dNotMutex, hsClosure);
                        }
                    }

                }
            }

        }
        public Dictionary<Predicate, HashSet<Predicate>> IdentifyMutexSAS(Problem problem,State initialState)
        {
            Dictionary<Predicate, HashSet<Predicate>> dMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            List<List<string>> lVariables = GetSASVariables(problem, initialState);
           
            foreach (List<string> lVariableAtoms in lVariables)
            {
                List<GroundedPredicate> lPredicates = new List<GroundedPredicate>();
                foreach (string sAtom in lVariableAtoms)
                {
                    string[] aAtom = sAtom.Split(new char[] { '(', ',', ')', ' ' }, StringSplitOptions.RemoveEmptyEntries);
                    Predicate pAtom = null;
                    List<Constant> lConstants = new List<Constant>();
                    foreach (Predicate p in Predicates)
                    {
                        if (p.Name == aAtom[0])
                        {
                            pAtom = p;
                        }
                    }
                    for (int i = 1; i < aAtom.Length; i++)
                    {
                        foreach (Constant c in Constants)
                        {
                            if (c.Name == aAtom[i])
                                lConstants.Add(c);
                        }
                    }
                    GroundedPredicate gp = null;
                    if (pAtom is GroundedPredicate)
                        gp = (GroundedPredicate)pAtom;
                    else
                    {
                        gp = new GroundedPredicate(pAtom.Name);
                        foreach (Constant c in lConstants)
                            gp.AddConstant(c);
                    }
                    lPredicates.Add(gp);
                    dMutex[gp] = new HashSet<Predicate>();
                }
                foreach (GroundedPredicate gp in lPredicates)
                {
                    foreach (GroundedPredicate gpOther in lPredicates)
                    {
                        if (gp != gpOther)
                            dMutex[gp].Add(gpOther);
                    }

                }
            }
            return dMutex;
        }



        private List<List<string>> GetSASVariables(Problem problem, State initialState)
        {
            MemoryStream msDomain = WriteSimpleDomain();
            StreamReader srOps = new StreamReader(msDomain);
            MemoryStream problem_M_S = problem.WriteSimpleProblem(initialState);
            StreamReader srFct = new StreamReader(problem_M_S);
            StreamWriter sw = new StreamWriter("TempDomain.pddl",false);
            StreamWriter sw2 = new StreamWriter("TempProblem.pddl", false);
            sw.Write(srOps.ReadToEnd());
            sw2.Write(srFct.ReadToEnd());
            sw.Close();
            sw2.Close();

            Process p = new Process();
            p.StartInfo.WorkingDirectory = Directory.GetCurrentDirectory();
            //p.StartInfo.FileName = Program.BASE_PATH + @"\PDDL\Planners\ff.exe";
            p.StartInfo.FileName = @"D:\Python27\Python.exe";
            p.StartInfo.Arguments =  "\""+Directory.GetCurrentDirectory()+@"\translate\translate.py"+ "\""; 
            //@"C:\PlanerFolder\translate\translate.py";
            p.StartInfo.Arguments += " TempDomain.pddl TempProblem.pddl";
            //p.StartInfo.WorkingDirectory = @"D:\Research\projects\PDDL\Planners\FD\translate";
            //p.StartInfo.WorkingDirectory = sPath;
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.RedirectStandardOutput = true;
            p.Start();
            p.WaitForExit();

            List<List<string>> lVariables = new List<List<string>>();
            StreamReader srSAS = new StreamReader("output.sas");
            string ss = srSAS.ReadToEnd();
            while (!srSAS.EndOfStream)
            {
                string sLine = srSAS.ReadLine().Trim();
                if (sLine == "begin_variable")
                {
                    bool bVarEnded = false;
                    List<string> lAtoms = new List<string>();
                    while (!srSAS.EndOfStream && !bVarEnded)
                    {
                        string sAtomLine = srSAS.ReadLine().Trim();
                        if (sAtomLine.StartsWith("Atom"))
                        {
                            lAtoms.Add(sAtomLine.Replace("Atom ", ""));

                        }
                        if (sAtomLine == "end_variable")
                            bVarEnded = true;
                    }
                    lVariables.Add(lAtoms);
                }

            }
           // throw new NotImplementedException();
            return lVariables;
            

        }

        public bool ParentOf(string sType1, string sType2)
        {
            if (sType1 == sType2)
                return true;
            if (TypeHierarchy.ContainsKey(sType2))
                return ParentOf(sType1, TypeHierarchy[sType2]);
            return false;
        }

        public void ComputePrivateActions()
        {
            //may need to compute private predicates - if a predicate uses a private object, then it is private, but this can be done only after grounding - not doing for now
            PrivateActions = new HashSet<Action>();
            PublicActions = new HashSet<Action>();
            foreach (Action a in Actions)
            {
                bool bPublic = false;
                if (a.Effects != null)
                {
                    foreach (Predicate p in a.Effects.GetAllPredicates())
                    {
                        foreach (Predicate pPublic in PublicPredicates)
                        {
                            if (p.Name == pPublic.Name)
                            {
                                bPublic = true;
                                break;
                            }
                        }
                    }

                }
                if (bPublic)
                    PublicActions.Add(a);
                else
                    PrivateActions.Add(a);
            }


            
        }

        public List<Action> GetProjectedPublicActions()
        {
            List<Action> lActions = new List<Action>();
            foreach (Action a in PublicActions)
            {
                Action aNew = new Action(a.Name);
                if(a.Preconditions != null)
                    aNew.Preconditions = a.Preconditions.FilterPredicates(PrivatePredicates);
                if (a.Effects != null)
                    aNew.Effects = a.Effects.FilterPredicates(PrivatePredicates);
                if (a.Observe != null)
                    throw new NotImplementedException();
                lActions.Add(aNew);
            }
            return lActions;
        }
    }
}
