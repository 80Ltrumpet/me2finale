//! # "Interesting Facts" Source
//!
//! This example queries and computes the statistics found in the README.
//!
//! ## Usage
//!
//! `cargo run [--release] --example analyze -- PATH`
//!
//! - `PATH` is a path to a file containing previously generated outcome data.

use std::collections::HashMap;
use std::error::Error;
use std::fs::File;

use rmp_serde::Deserializer;
use serde::Deserialize;

use me2finale::prelude::*;

fn main() -> Result<(), Box<dyn Error>> {
    let Some(path) = std::env::args().nth(1) else {
        return Err("PATH argument is required".into());
    };

    println!("Loading outcome data...");
    let file = File::open(&path)?;
    let mut deserializer = Deserializer::new(file);
    let outcome_map = OutcomeMap::deserialize(&mut deserializer)?;

    println!();

    let total_decision_paths = outcome_map
        .values()
        .map(|metadata| metadata.count)
        .sum::<usize>();
    println!("There are {total_decision_paths} total decision paths.");

    let total_outcomes = outcome_map.len();
    println!("There are {total_outcomes} total outcomes.");

    println!();

    // Which outcomes can only be achieved with one specific decision path?
    {
        let unique_outcomes = outcome_map
            .iter()
            .filter_map(|(outcome, metadata)| (metadata.count == 1).then_some(outcome))
            .collect::<Vec<_>>();
        let unique_outcome_count = unique_outcomes.len();
        println!("{unique_outcome_count} outcomes are uniquely achievable.");

        // Are there any commonalities between the unique outcomes?
        let mut common_survivors = AllySet::EVERYONE;
        let mut common_victims = AllySet::EVERYONE;
        let mut common_loyal = AllySet::EVERYONE;
        let mut common_disloyal = AllySet::EVERYONE;
        let mut common_crew: Result<bool, bool> = Err(true);
        for outcome in unique_outcomes {
            common_survivors &= outcome.survivors;
            common_victims -= outcome.survivors;
            common_loyal &= outcome.loyal;
            common_disloyal -= outcome.loyal;
            match common_crew {
                Ok(crew) => {
                    if crew != outcome.rescued_crew {
                        common_crew = Err(false);
                    }
                }
                Err(true) => common_crew = Ok(outcome.rescued_crew),
                Err(false) => {}
            }
        }

        println!("The unique outcomes have the following commonalities:");
        println!("- Survivors: {common_survivors}");
        println!("- Victims:   {common_victims}");
        println!("- Loyal:     {common_loyal}");
        println!("- Disloyal:  {common_disloyal}");
        if let Ok(common_crew) = common_crew {
            let verb = if common_crew { "Rescued" } else { "Abandoned" };
            println!("- Crew:      {verb}");
        }
    }

    println!();

    // What is the outcome achievable by the most decision paths?
    {
        let (most_common_outcome, max_metadata) = outcome_map
            .iter()
            .max_by_key(|(_, metadata)| metadata.count)
            .expect("`outcome_map` is not empty");
        let max_decision_paths = max_metadata.count;
        println!("The most common outcome can be achieved in {max_decision_paths} ways:");
        println!("{most_common_outcome}");
    }

    // How many decision paths lead to the top X outcomes?
    {
        let mut decision_path_counts = outcome_map
            .values()
            .map(|metadata| metadata.count)
            .collect::<Vec<_>>();
        decision_path_counts.sort();

        let mut decision_path_counts = decision_path_counts.into_iter().rev();

        let mut top_x_count = decision_path_counts.by_ref().take(10).sum::<usize>();
        println!("The ten most common outcomes cover {top_x_count} decision paths.");

        top_x_count += decision_path_counts.by_ref().take(90).sum::<usize>();
        println!("The one hundred most common outcomes cover {top_x_count} decision paths.");

        top_x_count += decision_path_counts.take(900).sum::<usize>();
        println!("The one thousand most common outcomes cover {top_x_count} decision paths.");
    }

    println!();

    // In how many ways can you fail the final mission (i.e., Shepard dies)?
    {
        let (failed_outcome_count, failed_decision_path_count) = outcome_map
            .iter()
            .filter_map(|(outcome, metadata)| {
                (outcome.survivors.len() < 2).then_some(metadata.count)
            })
            .enumerate()
            // This is a cheeky way to calculate a count and a sum with the same iterator.
            .fold((0, 0), |(_, sum), (i, count)| (i, sum + count));
        print!("There are {failed_outcome_count} outcomes in which Shepard dies, covering ");
        println!("{failed_decision_path_count} decision paths.");

        let shepard_survivals = total_decision_paths - failed_decision_path_count;
        let shepard_survival_rate = shepard_survivals as f32 / total_decision_paths as f32;
        let shepard_survival_percent = 100. * shepard_survival_rate;
        println!("- Shepard survives {shepard_survival_percent:.2}% of all decision paths.");
    }

    println!();

    // What does it take to achieve the "best" possible outcome?
    {
        // Morinth and Samara are mutually exclusive, and replacing Samara with Morinth leads to
        // negative consequences in Mass Effect 3. Therefore, the "best" outcome excludes Morinth.
        let best_outcome = Outcome {
            survivors: !Ally::Morinth,
            loyal: !Ally::Morinth,
            rescued_crew: true,
        };
        println!("The best possible outcome is defined as:\n{best_outcome}");

        if let Some(metadata) = outcome_map.get(&best_outcome) {
            println!(
                "There are {} ways to achieve the best possible outcome.",
                metadata.count
            );
            println!("Here is one example:");
            println!();
            print!("{}", metadata.example);
        } else {
            println!("There is no way to achieve the best possible outcome. :(");
        }
    }

    println!();

    // Create a table of absolute ally survival rates.
    {
        #[derive(Default)]
        struct SurvivalCounts {
            loyal: usize,
            disloyal: usize,
        }

        struct SurvivalRates {
            loyal: f32,
            disloyal: f32,
            total: f32,
        }

        let mut survival_counts: HashMap<_, SurvivalCounts> =
            HashMap::with_capacity(AllySet::EVERYONE.len());
        for (outcome, metadata) in outcome_map.iter() {
            for ally in outcome.survivors {
                match outcome.loyal.contains(ally) {
                    true => survival_counts.entry(ally).or_default().loyal += metadata.count,
                    false => survival_counts.entry(ally).or_default().disloyal += metadata.count,
                }
            }
        }
        let survival_counts = survival_counts;

        // Sort the table rows by descending total survival rate.
        let table_row_order = {
            let mut ally_and_total_survival = survival_counts
                .iter()
                .map(|(&ally, counts)| (ally, counts.loyal + counts.disloyal))
                .collect::<Vec<_>>();
            ally_and_total_survival.sort_by_key(|&(_, total)| total);
            ally_and_total_survival
                .into_iter()
                .rev()
                .map(|(ally, _)| ally)
                .collect::<Vec<_>>()
        };

        let absolute_survival_rates = survival_counts
            .into_iter()
            .map(|(ally, counts)| {
                let rates = SurvivalRates {
                    loyal: counts.loyal as f32 / total_decision_paths as f32,
                    disloyal: counts.disloyal as f32 / total_decision_paths as f32,
                    total: (counts.loyal + counts.disloyal) as f32 / total_decision_paths as f32,
                };
                (ally, rates)
            })
            .collect::<HashMap<_, _>>();

        println!("┌────────────────────────────────────────┐");
        println!("│      Absolute Ally Survival Rates      │");
        println!("╞═════════╤═════════╤══════════╤═════════╡");
        println!("│  Ally   │  Loyal  │ Disloyal │  Total  │");
        println!("├─────────┼─────────┼──────────┼─────────┤");
        for ally in table_row_order {
            if let Some(rates) = absolute_survival_rates.get(&ally) {
                print!("│ {:7} │ {:7.5} ", ally.name(), rates.loyal);
                println!("│  {:7.5} │ {:7.5} │", rates.disloyal, rates.total);
            } else {
                println!("│ {:7} │   ───   │   ────   │   ───   │", ally.name());
            }
        }
        println!("└─────────┴─────────┴──────────┴─────────┘");
    }

    Ok(())
}
