---
title: "On battery storage"
---

We want to switch to $$CO_2$$ neutral energy sources, but the sun doesn't always shine and the wind doesn't always blow. How much energy storage do we need to make the switch?

Let's consider The Netherlands, where I am from. In the winter, the energy production of solar panels is negligible. We sometimes have 2 week periods without any appreciable wind. How much energy storage do we need to make it through these periods, without everyone freezing to death?

### Assumptions

1. **Total Annual Energy Consumption**: The Netherlands' total annual energy consumption is 3500 PJ. More of this may be used in the winter, but let's conservatively use an average.
2. **Population**: The Netherlands' population is 17.5 million.
3. **Household Size**: Let's assume 3 people.
4. **Duration of Energy Shortfall**: A two-week period minimum. This would still be pretty scary, but let's use 14 days.
5. **Capacity of Tesla Powerwall**: Each Powerwall has a storage capacity of 13.5 kWh.

### Calculations

Convert the energy consumption in PJ to kWh:

$$
\text{Annual Dutch Consumption} = 3500 \, \text{PJ} \times 10^{15} \, \text{J/PJ} \times \frac{1}{3.6 \times 10^6}\, \text{kWh/J} \approx 972 \cdot 10^9 \text{ kWh}
$$

The average daily energy consumption per household:

$$
\text{Daily Household Consumption} = \frac{\text{Annual Dutch Consumption}}{365 \, \text{days} \times \text{Population}} \times \text{Household Size} \approx 456.6 \, \text{kWh}
$$

The number of Tesla Powerwalls needed:

$$
\text{Number of Powerwalls} = \frac{\text{Daily Household Consumption} \times 14 \, \text{days}}{\text{Powerwall Capacity}} \approx 473.5 \, \text{Powerwalls}
$$

### Conclusion

We need a large number of Tesla Powerwalls to meet energy needs during a two-week period of minimal renewable energy production. Note that this also includes industrial energy transitively required by the household, so the powerwalls wouldn't necessarily be installed at their house.

Clearly, the average household cannot afford to buy 473 Powerwalls. Even if discounted to €10,000 per powerwall and if we only needed 200, and with a 20 year Powerwall lifespan, this would still be €100,000 per household per year just for energy storage. We need either significantly cheaper battery technology, a different energy storage technology (e.g., methane synthesis), or the energy shortfall needs to be covered by a different source, such as nuclear energy.