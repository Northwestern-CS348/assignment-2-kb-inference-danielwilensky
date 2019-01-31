import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f) #why can't just use fact_rule here, i.e. don't need ind?
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        deleted = False
        if isinstance(fact_or_rule,Fact):
            if fact_or_rule in self.facts:
                ind = self.facts.index(fact_or_rule)
                fact = self.facts[ind]
                if fact.asserted == True:
                    fact.asserted=False
                    if len(fact.supported_by) == 0:
                        del self.facts[ind]
                        deleted=True
                else:
                    if len(fact.supported_by) == 0: #if not asserted should I still check if supported?
                        del self.facts[ind]
                        deleted=True
                if deleted:
                    for i in fact.supports_facts:
                        for j in i.supported_by:
                            if j[0] == fact:
                                ind2 = self.facts.index(i)
                                fact2 = self.facts[ind2]
                                fact2.supported_by.remove(j) #need to remove a tuple of [fact,rule]!!!!!!!!!
                                if len(fact2.supported_by)==0:
                                    self.kb_retract(fact2)
                    for i in fact.supports_rules:
                        for j in i.supported_by:
                            if j[0] == fact:
                                ind2 = self.rules.index(i)
                                rule2 = self.rules[ind2]
                                rule2.supported_by.remove(j)
                                if len(rule2.supported_by)==0:
                                    self.kb_retract(rule2)
        elif isinstance(fact_or_rule,Rule): #says rules can be retracted in Readme, but in piazza no???
            if fact_or_rule in self.rules:
                ind = self.rules.index(fact_or_rule)
                rule = self.rules[ind]
                if rule.asserted == False:
                    if len(rule.supported_by) == 0:
                        del self.rules[ind]
                        deleted=True
                if deleted:
                    for i in rule.supports_facts:
                        for j in i.supported_by:
                            if j[1] == rule:
                                ind2 = self.facts.index(i)
                                fact2 = self.facts[ind2]
                                fact2.supported_by.remove(j)
                                if len(fact2.supported_by)==0:
                                    self.kb_retract(fact2)
                    for i in rule.supports_rules:
                        for j in i.supported_by:
                            if j[1] == rule:
                                ind2 = self.facts.index(i)
                                rule2 = self.facts[ind2]
                                rule2.supported_by.remove(j)
                                if len(rule2.supported_by)==0:
                                    self.kb_retract(rule2)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        # if fact.statement.predicate == 'motherof':
        #     if rule.rhs.predicate == 'grandmotherof':
        #         print('h')
        binding = match(fact.statement,rule.lhs[0])
        if binding != False:
            if len(rule.lhs)>1:
                terms = []
                for i in range(len(rule.lhs)-1):
                    terms.append(instantiate(rule.lhs[i+1],binding)) #probs need to macth again, actually no
                terms = [terms,instantiate(rule.rhs,binding)]
                new_rule=Rule(terms) #create new rule with lhs w/o elt 0
                new_rule.supported_by.append([fact,rule])
                #new_rule.supported_by.append(fact)
                rule.supports_rules.append(new_rule)
                fact.supports_rules.append(new_rule)
                new_rule.asserted=False
                kb.kb_assert(new_rule)
            else: #lhs has 1 elt
                #probs need to match again, think not actually
                new_fact=Fact(instantiate(rule.rhs,binding)) #assuming rhs is only 1 thing always? yes
                new_fact.supported_by.append([fact,rule])
                #new_fact.supported_by.append(fact)
                rule.supports_facts.append(new_fact)
                fact.supports_facts.append(new_fact)
                new_fact.asserted=False
                kb.kb_assert(new_fact)
